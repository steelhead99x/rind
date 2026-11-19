# Algorithms

Whose code rind runs for each algorithm on each CPU, where that code comes
from and what of it is formally verified, and how the main paths work.
[PLATFORMS.md](PLATFORMS.md) lists the CPU features each architecture
requires.

Each cell names whose code runs on that path: the [sources](#sources) below,
rind's own code, or Graviola's. A ✓ marks code its source formally verifies,
to the extent [Sources](#sources) states, and a ⚡ unverified code chosen
because it measured faster than a verified alternative. An empty cell runs the
same sources as the one to its left. How fast each path runs, against
aws-lc-rs and ring, is in [BENCHMARKS.md's CPU tiers](BENCHMARKS.md#cpu-tiers);
the list under each table gives the reason wherever rind runs slower code by
choice.

x86_64 runs every feature. Each column to its right denies more, as
`bench.yml` describes: no AVX2 denies ADX, AVX2, BMI2, SHA-NI, AVX-512, VAES,
and VPCLMULQDQ (Sandy Bridge); no AVX also AVX (Westmere); no AES-NI also
AES-NI, PCLMULQDQ, and SSE4.1 (Core 2); and SSE2 also SSSE3. Without ADX
alone (Haswell), rind runs the same sources as x86_64, through s2n-bignum's
routines that don't use it, except that Ed25519 verification's
multiplication runs curve25519-dalek ⚡ (see below) and P-256 runs the no
AVX2 column's code.
CPUs with AVX2 but without SHA-NI run [OpenSSL]'s AVX2 SHA-256, and SLH-DSA's
SHA-2 sets [SPHINCS+]'s AVX2 eight-way SHA-256, and CPUs with the SHA512
instructions run OpenSSL's SHA-384 and SHA-512 for them. Intel CPUs
without AVX2 run [aws-lc]'s AVX SHA-1, SHA-256, and verified ✓ SHA-384 and
SHA-512. CPUs with AVX2 but without AVX-512 run ML-KEM-768's key generation
and decapsulation as ML-KEM-512's, on s2n-bignum ✓ + mlkem-native ✓, and only
its encapsulation on [verified-garbage] (see [ML-KEM](#ml-kem)). CPUs
without AVX-512 IFMA run X25519 and Ed25519 on s2n-bignum ✓ and rind's
glue, not verified-garbage (see [ECC](#ecc)), except that without ADX
Ed25519 verification's multiplication runs curve25519-dalek ⚡, as above.

| Algorithm | x86_64 | no AVX2 | no AVX | no AES-NI | SSE2 |
|---|---|---|---|---|---|
| AES-GCM | BoringSSL ⚡ + HACL* ✓ + Graviola | aws-lc + rind | Graviola | aws-lc + rind |  |
| AES block, AES-CTR | Graviola + aws-lc |  |  | aws-lc |  |
| AES-KW, AES-KWP | Graviola + rind |  |  | aws-lc + rind |  |
| AES-CBC | Graviola + aws-lc + rind |  |  | aws-lc + rind |  |
| ChaCha20 | verified-garbage ✓ + Graviola + HACL* ✓ | aws-lc + HACL* ✓ |  |  | HACL* ✓ |
| ChaCha20 (header protection) | HACL* ✓ + rind |  |  |  |  |
| ChaCha20-Poly1305, XChaCha20-Poly1305 | aws-lc ⚡ |  |  | HACL* ✓ + aws-lc ⚡ + Graviola ⚡ | HACL* ✓ + Graviola ⚡ |
| MD5 | rind |  |  |  |  |
| SHA-1 | rind | aws-lc |  |  |  |
| SHA-256 | Graviola ⚡ + rind ⚡ | aws-lc ⚡ |  |  |  |
| SHA-384, SHA-512, SHA-512/256 | OpenSSL ⚡ | aws-lc ⚡ |  |  |  |
| SHA3-256, SHA3-384, SHA3-512 | s2n-bignum ✓ + Graviola |  |  |  |  |
| HMAC | Graviola ⚡ |  |  |  |  |
| HKDF | rind ⚡ |  |  |  |  |
| HPKE, over the rows it builds on | rind |  |  |  |  |
| ECVRF, over the rows it builds on | rind |  |  |  |  |
| OPRF, VOPRF, over the rows it builds on | rind |  |  |  |  |
| FROST, over the rows it builds on | rind |  |  |  |  |
| PBKDF2 | rind |  |  |  |  |
| Argon2id | Argon2's reference + rind | rind |  |  |  |
| SPAKE2+ | rind, over P-256 |  |  |  |  |
| X25519 | verified-garbage |  |  |  |  |
| Ed25519 | verified-garbage |  |  |  |  |
| ristretto255 | s2n-bignum ✓ + rind |  |  |  |  |
| P-256 ECDH, ECDSA | verified-garbage + s2n-bignum ✓ + aws-lc + Graviola ⚡ | s2n-bignum ✓ + aws-lc + Graviola ⚡ |  |  |  |
| P-384 ECDH, ECDSA | s2n-bignum ✓ + rind ⚡ + Graviola ⚡ |  |  |  |  |
| P-521 ECDH, ECDSA | s2n-bignum ✓ + rind ⚡ |  |  |  |  |
| ML-KEM-512, ML-KEM-1024 | s2n-bignum ✓ + mlkem-native ✓ + Graviola ⚡ | mlkem-native ⚡ + s2n-bignum ✓ |  |  |  |
| ML-KEM-768 | verified-garbage | mlkem-native ⚡ + s2n-bignum ✓ + verified-garbage |  |  |  |
| ML-DSA-44, ML-DSA-65, ML-DSA-87 | s2n-bignum ✓ + mldsa-native ⚡ | mldsa-native ⚡ + s2n-bignum ✓ |  |  |  |
| SLH-DSA, over the SHA-2 and SHA-3 rows it builds on | SPHINCS+ |  |  |  |  |
| RSA signatures, OAEP, blind signatures, key generation | s2n-bignum ✓ + aws-lc ⚡ + rind ⚡ + verified-garbage | s2n-bignum ✓ + aws-lc ⚡ |  |  |  |

- RSA: x86_64 with ADX multiplies 1024- and 2048-bit moduli by
  [s2n-bignum]'s verified Karatsuba routines, as [#224] decided, rather than
  by [aws-lc]'s `bn_powerx5`, which led by up to 6% on an i7-8700 and trailed
  on Zen 3 and Zen 5. Without AVX2, it gathers each window entry by
  s2n-bignum's verified `bignum_copy_row_from_table` rather than, at widths
  that aren't a multiple of eight words, `bn_mul_mont_gather5`, which fuses
  a faster gather into the product. With AVX-512 IFMA, the public operation
  and the 2048- and 4096-bit private operation, and the 3072-bit one with
  AVX512_FP16, run [verified-garbage]'s routines (see [RSA](#rsa)).
- MD5: rind's portable Rust runs on every target, as no CPU has MD5
  instructions. On an i7-8700 it measured level with [aws-lc]'s x86_64
  assembly at 16 KB and 8% faster at 1350 B.
- AES-GCM key setup: a key reaches its cipher through an indirect call, so
  that a binary links only the ciphers it names; the call adds about 3 ns per
  key or 32 B seal.
- P-256 without ADX: verification runs s2n-bignum's verified routines rather
  than aws-lc's `ecp_nistz256`.
- P-256 on AMD CPUs with ADX but without AVX-512 IFMA, as Zen 3: a public
  key's derivation, and with it signing's nonce point, runs rind's own base
  point multiplication rather than verified-garbage's, which measured 1.02
  to 1.06× slower there (see [ECC](#ecc)).
- Ed25519 verification: rather than recompute `[S]B - [k]A` by s2n-bignum's
  verified `edwards25519_scalarmuldouble`, x86_64 checks `[v S]B - [v]R -
  [u]A = O` for scalars `u ≡ v k (mod 8L)` of about 128 bits, after
  ElSheikh et al., ["Accelerating EdDSA Signature Verification with Faster
  Scalar Size Halving"][half-size] (TCHES 2025), which halves the doublings.
  Solving modulo `8L` rather than the paper's `L`, with `v` odd, makes it
  accept exactly what the plain check does, torsion included, as
  `mid::half_size` argues. Its split and its four-point multiplication are
  rind's, variable-time over public inputs, over s2n-bignum's verified point
  routines, and on CPUs with AVX2 but without ADX over a port of
  curve25519-dalek's AVX2 backend. On an Arrow Lake core under load, it
  verified in 0.72 to 0.73× aws-lc-rs's time against 0.89 to 0.92×, 0.77 to
  0.83× against 0.86 to 0.88× with ADX denied, and 0.93× against 1.10× with
  AVX2 denied as well. aarch64 keeps `edwards25519_scalarmuldouble_alt` until
  the half-size check measures faster there.
- ChaCha20-Poly1305 without AES-NI and on SSE2, which lack SSE4.1: rind runs
  Graviola's scalar Poly1305 there, and aws-lc BoringSSL's SSE2
  `poly1305_vec.c`, which rind doesn't port for CPUs older than Westmere.
- ML-DSA: the FIPS 204 construction, and without AVX2 the arithmetic, run a
  Rust port of [mldsa-native]'s C, outside its CBMC proofs, rather than
  [libcrux]'s ML-DSA, which measured slower at every parameter set, with
  AVX2 and on the portable backend (see [ML-DSA](#ml-dsa)).
- SLH-DSA: its SHAKE sets trail the [SPHINCS+] team's AVX2 C by up to 1.2x,
  as their four-way Keccak-f is s2n-bignum's verified one, which transposes
  its four states in and out on each call; XKCP's, which SPHINCS+ runs on
  states it keeps transposed, measured 7% faster per call (see
  [SLH-DSA](#slh-dsa)).

aarch64 runs with the crypto extension, the SHA-512 and SHA-3
instructions, and SVE2; no crypto denies them, as a Raspberry Pi 4 lacks
them. Without SVE2 alone, as on Apple's cores and Neoverse N1 and V1,
ChaCha20-Poly1305 runs the no crypto column's aws-lc ⚡. armv7
runs in 32-bit mode, with NEON and the crypto extension; without them it runs
the code [Symmetric cryptography](#symmetric-cryptography) names. portable is
the backend for every other architecture, for big-endian aarch64 and arm, and
for ARM cores before ARMv7, which CI runs on x86_64 under
`--cfg rind_portable`: armv7's code without NEON and the crypto extension,
with portable Rust in place of the assembly armv7 runs regardless.

| Algorithm | aarch64 | no crypto | armv7 | portable |
|---|---|---|---|---|
| AES-GCM | s2n-bignum + Graviola + rind | aws-lc + rind |  | aws-lc + rind |
| AES block, AES-CTR | Graviola + rind | aws-lc |  | aws-lc |
| AES-KW, AES-KWP, AES-CBC | Graviola + rind | aws-lc + rind |  | aws-lc + rind |
| ChaCha20 | Graviola |  | HACL* ✓ | HACL* ✓ |
| ChaCha20 (header protection) | HACL* ✓ + rind |  |  |  |
| ChaCha20-Poly1305, XChaCha20-Poly1305 | verified-garbage | aws-lc ⚡ | HACL* rounds + 32-bit-word rind | HACL* rounds + Graviola; 26-bit rind when `rind_limb` is 32 |
| MD5 | rind |  |  |  |
| SHA-1 | rind | aws-lc |  | rind |
| SHA-256 | aws-lc ⚡ | aws-lc | rind; aws-lc ⚡ with the crypto extension | rind; ESP-IDF Xtensa runs the 16-round body from IRAM |
| SHA-384, SHA-512, SHA-512/256 | aws-lc | aws-lc ✓ | rind | rolled rind |
| SHA3-256, SHA3-384, SHA3-512 | s2n-bignum ✓ + Graviola |  | OpenSSL ⚡ + Graviola | rind + Graviola |
| HMAC | Graviola ⚡ |  |  |  |
| HKDF | rind ⚡ |  |  |  |
| HPKE, over the rows it builds on | rind |  |  |  |
| ECVRF, over the rows it builds on | rind |  |  |  |
| OPRF, VOPRF, over the rows it builds on | rind |  |  |  |
| FROST, over the rows it builds on | rind |  |  |  |
| PBKDF2 | verified-garbage + rind | rind |  |  |
| Argon2id | rind |  |  |  |
| SPAKE2+ | rind, over P-256 |  |  |  |
| X25519 | s2n-bignum ✓ |  | BoringSSL ⚡ + curve25519-dalek ⚡ | curve25519-dalek ⚡ |
| Ed25519 | s2n-bignum ✓ + Graviola |  | curve25519-dalek ⚡ + rind ⚡ |  |
| ristretto255 | s2n-bignum ✓ + rind |  | curve25519-dalek | curve25519-dalek |
| P-256 ECDH, ECDSA | verified-garbage + s2n-bignum ✓ + Graviola |  | fiat-crypto ✓ + rind ⚡ + Graviola ⚡ | fiat-crypto ✓ + rind + Graviola ⚡ |
| P-384 ECDH, ECDSA | s2n-bignum ✓ + rind ⚡ + Graviola ⚡ |  | fiat-crypto ✓ + rind ⚡ | fiat-crypto ✓ + rind |
| P-521 ECDH, ECDSA | s2n-bignum ✓ + rind ⚡ |  | fiat-crypto ✓ + rind ⚡ |  |
| ML-KEM-512, ML-KEM-1024 | s2n-bignum ✓ + Graviola ⚡ |  | mlkem-native ⚡ + OpenSSL ⚡ + Graviola ⚡ | mlkem-native ⚡ + rind + Graviola ⚡ |
| ML-KEM-768 | s2n-bignum ✓ + Graviola ⚡ + verified-garbage | s2n-bignum ✓ + Graviola ⚡ | mlkem-native ⚡ + OpenSSL ⚡ + Graviola ⚡ | mlkem-native ⚡ + rind + Graviola ⚡ |
| ML-DSA-44, ML-DSA-65, ML-DSA-87 | s2n-bignum ✓ + mldsa-native ⚡ |  | mldsa-native ⚡ + OpenSSL ⚡ | mldsa-native ⚡ + rind |
| SLH-DSA, over the SHA-2 and SHA-3 rows it builds on | SPHINCS+ |  |  |  |
| RSA signatures, OAEP, blind signatures, key generation | s2n-bignum ✓ + aws-lc ⚡ + Graviola ⚡ |  | aws-lc ⚡ + Graviola ⚡ + rind ⚡ | Graviola ⚡ + rind ⚡ |

- AES header protection on aarch64 pays the same indirect call as AES-GCM
  key setup on x86_64.
- armv7: SHA-1 runs aws-lc's NEON or integer routine, which took 0.53 of
  rind's Rust SHA-1 time on a Cortex-A7. SHA-256, SHA-512, ChaCha20, and
  Poly1305 run rind's Rust, since stable Rust has no 32-bit Arm NEON or SHA
  intrinsics. On a Raspberry Pi 2B (Cortex-A7) it took 1.26 times aws-lc's
  NEON SHA-256 time, 2.14 times its SHA-512 time, and 1.44 times its
  ChaCha20-Poly1305 time at 16 KB, and 0.72 to 0.75 of it at 32 and 64 B. A
  [native 32-bit comparison](benchmarks/armv7-sha256.md) measured that
  assembly 1.2 to 2.2× faster than Graviola's SHA-256 and rind's SHA-1.
- portable, ESP-IDF Xtensa: SHA-256 is rind's own FIPS 180-4 compression,
  sixteen rounds unrolled and the schedule body run three times, in IRAM
  (`.iram1`). `K` is in `.dram1`. Nothing proves this body. The 16-word
  window follows Graviola's `generic::sha256`, and the round constants are
  `generic::sha256_k` (Joe Birr-Pixton); the rotates and the block load
  are Xtensa `asm!`. Host tests check the Rust fallback against
  FIPS 180-4, `generic::sha256`, and aws-lc. CAVP and ACVP on every other
  portable target run `generic::sha256`, and SHA-384/512 run the rolled
  loop in `generic::sha512` on every pointer width. The board's sha2
  known-answer run executed the Xtensa asm. A fully
  rolled loop here was slower than the previous unrolled body in IRAM on
  an ESP32-S3. At
  `3aaa3c6a`, on a Seeed XIAO ESP32-S3 with 80 MHz flash and three runs,
  long SHA-256 takes about 0.76× that HACL*-in-IRAM image and about
  0.65–0.74× main's flash HACL* from 1200 B to 16 KB. In that sha2 image
  the block symbol is 4,412 bytes, `.iram0.text` is 4,516 bytes above
  main, `K` is 256 bytes in DRAM, and the hold-style heap is 282,856
  bytes against main's 287,464. A standalone object probe of the same
  tree reported a 4,256-byte block and 4,357 bytes of IRAM sections; that
  probe is not the firmware image, and it is not a 156-byte shrink of it.
  HMAC and HKDF were not in that pass. Host tests of this body run the
  Rust `rotate_right` and `from_be_bytes` fallbacks, not the Xtensa asm.
  `admin/esp32s3-sha256-layout`
  requires, in the linked image at opt-level 3, the block and the driver in
  IRAM, `K` in `.dram1`, no call from the block, and no relocation into
  flash text. A debug build is not that promise. Every other portable
  target runs `generic::sha256`.
- portable: ChaCha20-Poly1305's Poly1305 is Graviola's 64-bit limbs when
  `rind_limb` is 64, including wasm32 with `wide-arithmetic`, and rind's
  26-bit limbs when `rind_limb` is 32. Neither counts
  its input, so a message is not limited to 2^32 bytes. SHA-3's, ML-KEM's, and
  ML-DSA's Keccak-f is rind's, s2n-bignum's Keccak spec in Rust, which
  [`proofs/`](proofs/README.md) proves is FIPS 202's KECCAK-f[1600]; it
  measured as fast as RustCrypto's and libcrux-sha3's, which nothing proves.
  RSA's Montgomery multiplication is rind's own: an interleaved loop below 16
  limbs, then a separate product and reduction, with Karatsuba from 32 limbs.
  Its scratch is on the stack, never on the heap as HACL*'s is.
- portable: RSA and the NIST curves run on 64-bit limbs on 64-bit targets,
  and on wasm32 built with the `wide-arithmetic` target feature (stable from
  Rust 1.101), and on armv7's 32-bit limbs on other 32-bit targets, where a
  64-bit limb's product would be a library call. On 64-bit limbs P-256 and
  P-384 run fiat-crypto's field and scalar arithmetic whole: LLVM keeps its
  carry chains in registers there, and on x86_64 armv7's P-256 loop widened
  to `u128` ran ECDH and verification no faster end to end. The 64-bit columns
  are the ones this table's portable column describes; 32-bit portable
  targets run armv7's sources.
- P-521 on armv7: rind and aws-lc-rs both run [fiat-crypto]'s field
  arithmetic, which spills no carry flag there. A `umaal` multiply ran more
  instructions in [#281], so rind keeps the verified code.

The table describes `main`, and changes alongside the code it describes. The
tests use [Wycheproof]'s vectors.

## Sources

| Source | How rind uses it | License | What is verified |
|---|---|---|---|
| [Graviola] | copied: rind began as a copy of it, and rind-rustls of its rustls-graviola; its aarch64 ChaCha20 and its Poly1305 began as [cifra], CC0-1.0; the ESP-IDF Xtensa SHA-256 window and round constants follow its `generic/sha256.rs` | Apache-2.0 OR ISC OR MIT-0 | nothing |
| rind | its own code | Apache-2.0 OR ISC OR MIT-0 | nothing |
| [Argon2's reference] | ported: its AVX2 BlaMka rounds, `blamka-round-opt.h`, to Rust intrinsics, for Argon2id on x86_64 CPUs with AVX2 | CC0-1.0 OR Apache-2.0, taken under CC0-1.0 | nothing |
| [s2n-bignum] | copied: its assembly for the elliptic curves, RSA, ML-KEM, ML-DSA, Keccak-f, and aarch64 AES-GCM, transliterated into Rust `asm!` by `admin/parse-asm`, which ends each x86_64 routine using 256-bit registers with `vzeroupper` | Apache-2.0 OR ISC OR MIT-0; its ML-KEM, ML-DSA, and aarch64 Keccak-f routines (from mlkem-native and mldsa-native) Apache-2.0 OR ISC OR MIT; its x86_64 single-state Keccak-f (from OpenSSL) Apache-2.0 | HOL Light proofs ([x86_64](https://github.com/awslabs/s2n-bignum/tree/3f01260ff1bd2577abf0117ce45aa008bc243a80/x86/proofs), [aarch64](https://github.com/awslabs/s2n-bignum/tree/3f01260ff1bd2577abf0117ce45aa008bc243a80/arm/proofs)) that each routine's object code computes its specified result for all inputs; some also prove that its memory accesses stay in bounds and that its branches and addresses depend on no secret. `admin/prove bytes` checks that rind's build of each routine holds the instructions its proof lists, with the differences [below](#s2n-bignums-constant-time-theorems), so the proofs are of rind's code. The aarch64 AES-GCM kernels' theorems cover the in-place calls rind makes. |
| [HACL\*] | copied, from libcrux-chacha20poly1305: the ChaCha20 rounds, for HChaCha20 and QUIC header protection and for x86_64's ChaCha20 up to one block, 128 bytes without AVX2, and every length without SSSE3, and every ChaCha20 length on the portable backend; armv7's ChaCha20 state words are rind's, RFC 8439, and its keystream is aws-lc; copied, by `admin/import-hacl`: Vale's x86_64 AES-GCM assembly, as Rust naked functions. Portable SHA-256, SHA-384/512, and Poly1305 are rind's, not this code | Apache-2.0; Vale's AES-GCM routines port OpenSSL's `aesni_gcm`, Apache-2.0 | [F\* proofs](https://github.com/hacl-star/hacl-star/tree/f557259007db9933442dde10aa995c1b00bd3446) of memory safety, functional correctness, and secret independence of the F\* source. libcrux's Rust is compiled mechanically from HACL\*'s verified C, and that step is not itself verified. rind's code that loads the rounds' state and XORs their keystream is not covered, except for header protection, which rind's own Lean proof covers with the rounds. Vale's [F\* proofs](https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/vale/code/arch/x64/interop/Vale.Wrapper.X64.GCMencryptOpt.fsti) that its x86_64 AES-GCM, as Vale prints it, computes AES-128-GCM and AES-256-GCM, tag check included, for any AAD and message under 2^32 bytes, in place or not, from the counter block its own routine computes, which rind runs for it, and the round keys and GHASH key powers its own routines compute. `admin/prove bytes` checks that rind's copies of the routines it runs assemble to the instructions of Vale's printed text. rind computes those keys and powers itself, and its tests check them byte for byte against Vale's routines. [`proofs/`](proofs/README.md) proves that code, and rind's Rust that splits the message into the routines' blocks and copies the partial ones, as EverCrypt's proven Low\* wrapper does, from its AEAD API down to Vale's routines. |
| [mlkem-native] | ported: its portable C polynomial arithmetic (the NTT, inverse NTT, base multiplication, reductions, byte encoding, and rejection sampling), to Rust, for armv7 and x86_64 CPUs without AVX2; copied, by `admin/import-aws-lc` from aws-lc's copy: its x86_64 AVX2 ciphertext compression at 4, 5, 10, and 11 bits, which rind ends with `vzeroupper` | Apache-2.0 OR ISC OR MIT | [CBMC proofs](https://github.com/pq-code-package/mlkem-native/tree/d1b2fe782888bdb761a50336012923180be7f502/proofs/cbmc) of memory safety and coefficient bounds for its C. They do not cover rind's port. [HOL Light proofs](https://github.com/pq-code-package/mlkem-native/tree/d1b2fe782888bdb761a50336012923180be7f502/proofs/hol_light/x86_64) that its AVX2 compression's object code computes its specified result for all inputs, of mlkem-native's own build, at the revision aws-lc's copy takes. |
| [mldsa-native] | ported: its C FIPS 204 construction (`sign.c`, `packing.c`, `poly.c`, and `poly_kl.c`) on every CPU, and its portable C polynomial arithmetic for armv7, the portable backend, and x86_64 CPUs without AVX2, to Rust, at v2.0.0 | Apache-2.0 OR ISC OR MIT | [CBMC proofs](https://github.com/pq-code-package/mldsa-native/tree/834a90d5e846ffa1e1611bd24e160bb2e9b86d35/proofs/cbmc) of memory safety and coefficient bounds for its C. They do not cover rind's port, which rind's tests check against s2n-bignum's routines, [Wycheproof], ACVP, and aws-lc-rs. |
| [aws-lc] | copied, by `admin/import-aws-lc`: its SHA-384/512 assembly for x86_64 and aarch64, its x86_64 AVX SHA-256 routine and its aarch64 one for the SHA-256 instructions, Montgomery multiplication and the x86_64 exponentiation's `bn_power5` (with one deliberate change: rind's `bn_sqr8x_mont` and `bn_powerx5` zero two scratch words their `mulx` squaring reads unwritten, which valgrind reports though results and timing do not depend on them), AVX2 and dual AVX-512 RSAZ exponentiation, AES-NI AES-CTR, P-256's mixed addition for its generator multiplication (with one deliberate change: rind's BMI2 and ADX copy drops the `.byte 0x67` address-size prefixes aws-lc pads two of its squaring's register-only `mulx` with, which the CPU ignores and s2n-bignum's x86 model does not decode), and SSE4.1 and AVX2 ChaCha20-Poly1305 (with one deliberate change: rind's copy reads the choice of AVX2 from the block rind passes it rather than aws-lc's `OPENSSL_ia32cap_P`), its aarch64 NEON ChaCha20-Poly1305 and eight-way AES-192-GCM, its x86_64 assembly for CPUs without AVX2 (SSSE3 ChaCha20, SSSE3 and AVX SHA-1, and SSSE3 SHA-256) without AES-NI (SSSE3 AES and GHASH), and without SSSE3 (integer SHA-1 and SHA-256), its aarch64 Montgomery multiplication, and its aarch64 assembly for CPUs without the crypto extension (NEON AES, NEON GHASH, and scalar SHA-1 and SHA-256), as Rust naked functions; its 32-bit ARM assembly for SHA-1 (NEON and integer), Montgomery multiplication, and the ARMv8 crypto extension (AES, GHASH, SHA-1, SHA-256), in Rust `global_asm!`; and the C that drives RSAZ, and `bn_power5`, that sets up its x86_64 SSSE3 GHASH table, and that computes its constant-time SSE2 AES and integer GHASH for x86_64 CPUs without SSSE3, ported to Rust, both also for armv7 without the crypto extension and the portable backend. aws-lc takes its Poly1305, ChaCha20-Poly1305, SSSE3 GHASH, and constant-time AES and GHASH from BoringSSL and the rest from OpenSSL | Apache-2.0; Poly1305, ChaCha20-Poly1305, SSSE3 and integer GHASH, and constant-time AES ISC | [SAW and NSym proofs](https://github.com/awslabs/aws-lc-verification/tree/797302470c1703cbb1a3a6fa98daffef0bfd3d80) that its x86_64 AVX and aarch64 scalar SHA-384/512 routines compute their specified result for all inputs. Their proof of its aarch64 routine for the SHA-512 instructions ends with the result in registers, before the routine stores it, so rind's own HOL Light proof covers that routine, of the object code rind's build emits, against s2n-bignum's FIPS 180-4 spec, and rind's own HOL Light proofs cover both forms of P-256's mixed addition, of the object code rind's Linux build emits, against s2n-bignum's P-256 group law. `admin/prove bytes` checks that rind's copies of the first two routines assemble to the instructions of aws-lc's text at the revision the proofs pin, so the proofs are of rind's code. They do not cover its 32-bit ARM code. [`proofs/`](proofs/README.md) proves rind's SHA-384/512 around the AVX and both aarch64 routines. |
| [BoringSSL] | copied, by `admin/import-boringssl`: its x86_64 VAES AES-GCM assembly, `aes-gcm-avx2-x86_64` and `aes-gcm-avx512-x86_64`, as Rust naked functions; its 32-bit ARM NEON X25519 assembly, in Rust `global_asm!`, which BoringSSL takes from [SUPERCOP]'s `neon2`, public domain | Apache-2.0 | nothing |
| [OpenSSL] | copied, by `admin/import-openssl`: its x86_64 AVX2 SHA-256 and SHA-512 assembly and its SHA-512 assembly for the SHA512 instructions, from `sha512-x86_64`, as Rust naked functions; its 32-bit ARM Keccak-f assembly, integer and NEON, `keccak1600-armv4`, in Rust `global_asm!` | Apache-2.0 | nothing |
| [SPHINCS+] | ported: the SPHINCS+ team's FIPS 205 code (`sign.c`, `fors.c`, `wots.c`, `merkle.c`, and its AVX2 builds' `treehashx4` and `treehashx8`, generalised over the lane count) on every CPU, and its x86_64 AVX2 eight-way SHA-256 (`sha256avx.c`), to Rust, from the `bas/fips205` branch | public domain, or CC0-1.0, 0BSD, or MIT-0 | nothing: no SLH-DSA implementation carries a proof of functional correctness |
| [curve25519-dalek] | dependency, with its serial backend, for armv7 and the portable backend; ported: its AVX2 backend's field arithmetic, point formulas, and base point table, to Rust intrinsics, for Ed25519 verification's four-point multiplication on x86_64 CPUs with AVX2 but without ADX | BSD-3-Clause | nothing: that backend's field arithmetic is hand-written, as is the AVX2 backend's. Its `fiat` backend would run [fiat-crypto]'s verified field arithmetic instead, but only a `--cfg` flag for the whole build selects it, so rind refuses it rather than let the build pick. |
| [fiat-crypto] | dependency | MIT OR Apache-2.0 OR BSD-1-Clause | [Coq proofs](https://github.com/mit-plv/fiat-crypto/tree/67316f05d771f7f2db62beede59e9b56406a9efd) that each generated field operation is correct. rind's point formulas, inversion, and table lookup over them are not covered. |
| [verified-garbage] | copied, by `admin/import-vg`: its aarch64 SVE2 ChaCha20-Poly1305 seal and open, with the ChaCha20 and Poly1305 routines they call, its x86_64 ChaCha20 from 256 bytes on AVX2 and on AVX-512 VL, its x86_64 X25519 and Ed25519 for AVX-512 IFMA, with the SHA-512 and field and point routines they call, its x86_64 RSA public operation and CRT for AVX-512 IFMA, with the Montgomery product they call, its ML-KEM-768 encapsulation key check and encapsulation on x86_64 and on aarch64 with the SHA-3 instructions, and key generation and decapsulation on x86_64 with AVX-512, its aarch64 PBKDF2 over HMAC-SHA1 and HMAC-SHA256 with the crypto extension and over HMAC-SHA384 and HMAC-SHA512 with the SHA-512 instructions, and its P-256 public key derivation, ECDH, and ECDSA verification on x86_64 with BMI2 and ADX, ECDH and verification also for AVX-512 IFMA, and on aarch64, with the Keccak, hash, arithmetic, and point routines and tables they call, as Rust naked functions, byte for byte but for `.base64` directives written out as `.byte`, which rind's minimum Rust cannot assemble; and, by `admin/import-vg-models` at the same commit, its Lean x86_64 and aarch64 ISA models, printers, and encoders, and the ML-KEM and SHA-3 specs, and the RSA and ChaCha20 specs and contracts, that rind's proofs import or adapt, under `proofs/verified-garbage/` | Apache-2.0 OR BSD-3-Clause; the models taken under Apache-2.0 | [Lean proofs](https://github.com/pyca/verified-garbage/tree/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean) that each routine's machine code meets its contract (RFC 8439's for ChaCha20-Poly1305, RFC 7748's and RFC 8032's for X25519 and Ed25519, FIPS 203's for ML-KEM-768), is memory safe, and takes the same branches and memory addresses whatever its secrets, over VG's own models of the instructions. The RSA routines rind runs are internal to VG, so their contracts are in its proofs rather than its trusted specification. `admin/prove vg` cosimulates those models for each instruction of VG's code, on the CPU or, where it lacks a feature, under Intel SDE or qemu-aarch64, but for `jmp`/`b`, static addresses, and a lone `ret`, which its bytes check covers, and checks that rind's copies are VG's text. rind claims no ✓ for this code until it imports the theorems: [`proofs/`](proofs/README.md) restates those of its x86_64 ChaCha20 as axioms, which so earns the ✓, and proves rind's Rust around them from 256 bytes, assuming the contract of rind's two-block AVX2 kernel, which runs a remainder of 65 to 255 bytes after the last whole 512-byte group, and that the CPU-feature checks find AVX2 or AVX-512 VL. It imports those of its x86_64 RSA routines and proves rind's RSA verification around them, and restates ML-KEM-768's as axioms, whose ✓ waits on a proof of rind's ML-KEM construction around them. |

rind's own code is licensed under Apache-2.0 OR ISC OR MIT-0. Copied code
keeps its source's copyright and license, which [LICENSE] lists with the
texts they require; dependencies ship their own. Every file under
`rind/src` names its license in a `SPDX-License-Identifier` comment, and
files Graviola wrote keep their `Written for Graviola by ...` header. The
`rind` crate as a whole is therefore `(Apache-2.0 OR ISC OR MIT-0) AND
(Apache-2.0 OR ISC OR MIT) AND Apache-2.0 AND ISC AND BSD-3-Clause`. The
adapter crates copy nothing under another license, so they stay
`Apache-2.0 OR ISC OR MIT-0`.
rind-ring runs ring's own tests, and rind-aws-lc-rs aws-lc-rs's, which keep
their sources' licenses and stay out of the published crates.

A change that copies code from a new source, or moves an algorithm to a
different one, updates this table and [LICENSE] in the same PR.

## s2n-bignum's constant-time theorems

s2n-bignum's `_SAFE` theorems prove, for every input, that the instructions a
routine executes and the addresses it accesses depend on no secret, and that
it runs no instruction whose timing depends on its operands. `admin/prove
bytes`, in the `prove` workflow, checks that each routine's `asm!` block in
rind's release build holds the instructions its proof lists, upstream's
proof at the base commit of rind's fork, `thirdparty/s2n-bignum`, so those
theorems are about the code rind runs. A block
differs from its proof's code only as `admin/prove-bytes` lists, none of the
changes altering the result the proof states or making a branch, address, or
timing depend on a secret: the final `ret` is gone, as the Rust function
returns; an x86_64 routine using 256-bit registers ends with `vzeroupper`; an
aarch64 routine has no `BTI c`, as in the code the `_NOIBT_` theorems cover; a
routine returning from several places, or whose local subroutines follow its
`ret`, branches to the block's end from each such `ret`; and LLVM's assembler
writes some commutative x86_64 instructions with their sources swapped.

The table names, for each Rust function rind transliterates from s2n-bignum,
the routine it runs on each target and the subroutine `_SAFE` theorem that
covers it, or "none" where s2n-bignum proves none at the pinned revision.
LLVM may inline `bignum_modadd`, which a hot loop calls, so no symbol marks
its copies and the check does not reach them; the check fails if such a
routine has a `_SAFE` theorem.
`admin/ct-binsec` checks those in the loop, `PosInt::reduce_even`, with
BINSEC.

<!-- admin/prove-bytes inventory -->
| Function | x86_64 | aarch64 |
|---|---|---|
| `aes128_gcm_dec` | not imported | `aes128_gcm_dec`: `AES128_GCM_DEC_NOIBT_SUBROUTINE_SAFE` |
| `aes128_gcm_dec_alt` | not imported | `aes128_gcm_dec_alt`: `AES128_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE` |
| `aes128_gcm_enc` | not imported | `aes128_gcm_enc`: `AES128_GCM_ENC_NOIBT_SUBROUTINE_SAFE` |
| `aes128_gcm_enc_alt` | not imported | `aes128_gcm_enc_alt`: `AES128_GCM_ENC_ALT_NOIBT_SUBROUTINE_SAFE` |
| `aes256_gcm_dec` | not imported | `aes256_gcm_dec`: `AES256_GCM_DEC_NOIBT_SUBROUTINE_SAFE` |
| `aes256_gcm_dec_alt` | not imported | `aes256_gcm_dec_alt`: `AES256_GCM_DEC_ALT_NOIBT_SUBROUTINE_SAFE` |
| `aes256_gcm_enc` | not imported | `aes256_gcm_enc`: `AES256_GCM_ENC_NOIBT_SUBROUTINE_SAFE` |
| `aes256_gcm_enc_alt` | not imported | `aes256_gcm_enc_alt`: `AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_SAFE` |
| `bignum_add` | `bignum_add`: none | `bignum_add`: none |
| `bignum_add_p25519` | `bignum_add_p25519`: none | `bignum_add_p25519`: none |
| `bignum_add_p256` | `bignum_add_p256`: none | `bignum_add_p256`: none |
| `bignum_add_p384` | `bignum_add_p384`: `BIGNUM_ADD_P384_SUBROUTINE_SAFE` | `bignum_add_p384`: `BIGNUM_ADD_P384_SUBROUTINE_SAFE` |
| `bignum_add_p521` | `bignum_add_p521`: `BIGNUM_ADD_P521_SUBROUTINE_SAFE` | `bignum_add_p521`: `BIGNUM_ADD_P521_SUBROUTINE_SAFE` |
| `bignum_bitsize` | `bignum_bitsize`: none | `bignum_bitsize`: none |
| `bignum_cmp_lt` | `bignum_lt`: none | `bignum_lt`: none |
| `bignum_coprime` | `bignum_coprime`: none | `bignum_coprime`: none |
| `bignum_copy_row_from_table` | `bignum_copy_row_from_table`: none | `bignum_copy_row_from_table`: `BIGNUM_COPY_ROW_FROM_TABLE_SUBROUTINE_SAFE` |
| `bignum_copy_row_from_table_16` | not imported | `bignum_copy_row_from_table_16`: `BIGNUM_COPY_ROW_FROM_TABLE_16_SUBROUTINE_SAFE` |
| `bignum_copy_row_from_table_32` | not imported | `bignum_copy_row_from_table_32`: `BIGNUM_COPY_ROW_FROM_TABLE_32_SUBROUTINE_SAFE` |
| `bignum_copy_row_from_table_8n` | not imported | `bignum_copy_row_from_table_8n`: `BIGNUM_COPY_ROW_FROM_TABLE_8N_SUBROUTINE_SAFE` |
| `bignum_ctz` | `bignum_ctz`: none | `bignum_ctz`: none |
| `bignum_demont` | `bignum_demont`: none | `bignum_demont`: none |
| `bignum_demont_p256` | `bignum_demont_p256`: none | `bignum_demont_p256`: none |
| `bignum_demont_p256_alt` | `bignum_demont_p256_alt`: none | not imported |
| `bignum_demont_p384` | `bignum_demont_p384`: none | `bignum_demont_p384`: none |
| `bignum_demont_p384_alt` | `bignum_demont_p384_alt`: none | not imported |
| `bignum_digitsize` | `bignum_digitsize`: none | `bignum_digitsize`: none |
| `bignum_emontredc_8n` | `bignum_emontredc_8n`: none | not imported |
| `bignum_eq` | `bignum_eq`: none | `bignum_eq`: none |
| `bignum_inv_p256` | `bignum_inv_p256`: none | `bignum_inv_p256`: none |
| `bignum_inv_p384` | `bignum_inv_p384`: none | `bignum_inv_p384`: none |
| `bignum_inv_p521` | `bignum_inv_p521`: `BIGNUM_INV_P521_SUBROUTINE_SAFE` | `bignum_inv_p521`: `BIGNUM_INV_P521_SUBROUTINE_SAFE` |
| `bignum_invsqrt_p25519` | `bignum_invsqrt_p25519`: none | `bignum_invsqrt_p25519_alt`: none |
| `bignum_invsqrt_p25519_alt` | `bignum_invsqrt_p25519_alt`: none | not imported |
| `bignum_kmul_16_32` | `bignum_kmul_16_32`: none | not imported |
| `bignum_kmul_32_64` | `bignum_kmul_32_64`: none | not imported |
| `bignum_ksqr_16_32` | `bignum_ksqr_16_32`: none | not imported |
| `bignum_ksqr_32_64` | `bignum_ksqr_32_64`: none | not imported |
| `bignum_madd_n25519` | `bignum_madd_n25519`: `BIGNUM_MADD_N25519_SUBROUTINE_SAFE` | `bignum_madd_n25519_alt`: `BIGNUM_MADD_N25519_ALT_SUBROUTINE_SAFE` |
| `bignum_madd_n25519_alt` | `bignum_madd_n25519_alt`: `BIGNUM_MADD_N25519_ALT_SUBROUTINE_SAFE` | not imported |
| `bignum_mod_n25519` | `bignum_mod_n25519`: `BIGNUM_MOD_N25519_SUBROUTINE_SAFE` | `bignum_mod_n25519`: `BIGNUM_MOD_N25519_SUBROUTINE_SAFE` |
| `bignum_mod_n256` | `bignum_mod_n256_4`: none | `bignum_mod_n256_4`: none |
| `bignum_mod_n384` | `bignum_mod_n384_6`: none | `bignum_mod_n384_6`: none |
| `bignum_mod_n521` | `bignum_mod_n521_9`: `BIGNUM_MOD_N521_9_SUBROUTINE_SAFE` | `bignum_mod_n521_9`: `BIGNUM_MOD_N521_9_SUBROUTINE_SAFE` |
| `bignum_mod_n521_alt` | `bignum_mod_n521_9_alt`: `BIGNUM_MOD_N521_9_ALT_SUBROUTINE_SAFE` | not imported |
| `bignum_modadd` | `bignum_modadd`: none; inlinable, so unchecked | `bignum_modadd`: none; inlinable, so unchecked |
| `bignum_modinv` | `bignum_modinv`: none | `bignum_modinv`: none |
| `bignum_modsub` | `bignum_modsub`: none | `bignum_modsub`: none |
| `bignum_montifier` | `bignum_montifier`: none | `bignum_montifier`: none |
| `bignum_montmul` | `bignum_montmul`: none | `bignum_montmul`: none |
| `bignum_montmul_p256` | `bignum_montmul_p256`: `BIGNUM_MONTMUL_P256_SUBROUTINE_SAFE` | `bignum_montmul_p256_alt`: none |
| `bignum_montmul_p256_alt` | `bignum_montmul_p256_alt`: none | not imported |
| `bignum_montmul_p384` | `bignum_montmul_p384`: `BIGNUM_MONTMUL_P384_SUBROUTINE_SAFE` | `bignum_montmul_p384_alt`: `BIGNUM_MONTMUL_P384_ALT_SUBROUTINE_SAFE` |
| `bignum_montmul_p384_alt` | `bignum_montmul_p384_alt`: `BIGNUM_MONTMUL_P384_ALT_SUBROUTINE_SAFE` | not imported |
| `bignum_montredc` | `bignum_montredc`: none | `bignum_montredc`: none |
| `bignum_montsqr` | not imported | `bignum_montsqr`: none |
| `bignum_montsqr_p256` | `bignum_montsqr_p256`: `BIGNUM_MONTSQR_P256_SUBROUTINE_SAFE` | `bignum_montsqr_p256_alt`: none |
| `bignum_montsqr_p256_alt` | `bignum_montsqr_p256_alt`: none | not imported |
| `bignum_montsqr_p384` | `bignum_montsqr_p384`: `BIGNUM_MONTSQR_P384_SUBROUTINE_SAFE` | `bignum_montsqr_p384_alt`: `BIGNUM_MONTSQR_P384_ALT_SUBROUTINE_SAFE` |
| `bignum_montsqr_p384_alt` | `bignum_montsqr_p384_alt`: `BIGNUM_MONTSQR_P384_ALT_SUBROUTINE_SAFE` | not imported |
| `bignum_mul` | `bignum_mul`: none | `bignum_mul`: `BIGNUM_MUL_SUBROUTINE_SAFE` |
| `bignum_mul_p25519` | `bignum_mul_p25519`: none | `bignum_mul_p25519_alt`: none |
| `bignum_mul_p25519_alt` | `bignum_mul_p25519_alt`: none | not imported |
| `bignum_mul_p521` | `bignum_mul_p521`: `BIGNUM_MUL_P521_SUBROUTINE_SAFE` | `bignum_mul_p521_alt`: `BIGNUM_MUL_P521_ALT_SUBROUTINE_SAFE` |
| `bignum_mul_p521_alt` | `bignum_mul_p521_alt`: `BIGNUM_MUL_P521_ALT_SUBROUTINE_SAFE` | not imported |
| `bignum_mux` | `bignum_mux`: none | `bignum_mux`: none |
| `bignum_neg_p25519` | `bignum_neg_p25519`: `BIGNUM_NEG_P25519_SUBROUTINE_SAFE` | `bignum_neg_p25519`: `BIGNUM_NEG_P25519_SUBROUTINE_SAFE` |
| `bignum_neg_p256` | `bignum_neg_p256`: none | `bignum_neg_p256`: none |
| `bignum_neg_p384` | `bignum_neg_p384`: `BIGNUM_NEG_P384_SUBROUTINE_SAFE` | `bignum_neg_p384`: `BIGNUM_NEG_P384_SUBROUTINE_SAFE` |
| `bignum_neg_p521` | `bignum_neg_p521`: `BIGNUM_NEG_P521_SUBROUTINE_SAFE` | `bignum_neg_p521`: `BIGNUM_NEG_P521_SUBROUTINE_SAFE` |
| `bignum_negmodinv` | `bignum_negmodinv`: none | `bignum_negmodinv`: none |
| `bignum_optsub` | `bignum_optsub`: none | `bignum_optsub`: `BIGNUM_OPTSUB_SUBROUTINE_SAFE` |
| `bignum_sqr_p25519` | `bignum_sqr_p25519`: none | `bignum_sqr_p25519_alt`: none |
| `bignum_sqr_p25519_alt` | `bignum_sqr_p25519_alt`: none | not imported |
| `bignum_sqr_p521` | `bignum_sqr_p521`: `BIGNUM_SQR_P521_SUBROUTINE_SAFE` | `bignum_sqr_p521_alt`: `BIGNUM_SQR_P521_ALT_SUBROUTINE_SAFE` |
| `bignum_sqr_p521_alt` | `bignum_sqr_p521_alt`: `BIGNUM_SQR_P521_ALT_SUBROUTINE_SAFE` | not imported |
| `bignum_sub_p25519` | `bignum_sub_p25519`: none | `bignum_sub_p25519`: none |
| `bignum_tomont_p256` | `bignum_tomont_p256`: none | `bignum_tomont_p256`: none |
| `bignum_tomont_p256_alt` | `bignum_tomont_p256_alt`: none | not imported |
| `bignum_tomont_p384` | `bignum_tomont_p384`: `BIGNUM_TOMONT_P384_SUBROUTINE_SAFE` | `bignum_tomont_p384`: `BIGNUM_TOMONT_P384_SUBROUTINE_SAFE` |
| `bignum_tomont_p384_alt` | `bignum_tomont_p384_alt`: `BIGNUM_TOMONT_P384_ALT_SUBROUTINE_SAFE` | not imported |
| `curve25519_x25519` | `curve25519_x25519`: `CURVE25519_X25519_SUBROUTINE_SAFE` | `curve25519_x25519_byte_alt`: `CURVE25519_X25519_BYTE_ALT_SUBROUTINE_SAFE` |
| `curve25519_x25519_alt` | `curve25519_x25519_alt`: `CURVE25519_X25519_ALT_SUBROUTINE_SAFE` | not imported |
| `curve25519_x25519base` | `curve25519_x25519base`: `CURVE25519_X25519BASE_SUBROUTINE_SAFE` | `curve25519_x25519base_byte_alt`: `CURVE25519_X25519BASE_BYTE_ALT_SUBROUTINE_SAFE` |
| `curve25519_x25519base_alt` | `curve25519_x25519base_alt`: `CURVE25519_X25519BASE_ALT_SUBROUTINE_SAFE` | not imported |
| `edwards25519_decode` | `edwards25519_decode`: `EDWARDS25519_DECODE_SUBROUTINE_SAFE` | `edwards25519_decode_alt`: `EDWARDS25519_DECODE_ALT_SUBROUTINE_SAFE` |
| `edwards25519_decode_alt` | `edwards25519_decode_alt`: `EDWARDS25519_DECODE_ALT_SUBROUTINE_SAFE` | not imported |
| `edwards25519_epadd` | `edwards25519_epadd`: none | `edwards25519_epadd_alt`: none |
| `edwards25519_epadd_alt` | `edwards25519_epadd_alt`: none | not imported |
| `edwards25519_epdouble` | `edwards25519_epdouble`: none | `edwards25519_epdouble_alt`: none |
| `edwards25519_epdouble_alt` | `edwards25519_epdouble_alt`: none | not imported |
| `edwards25519_pdouble` | `edwards25519_pdouble`: none | `edwards25519_pdouble_alt`: none |
| `edwards25519_pdouble_alt` | `edwards25519_pdouble_alt`: none | not imported |
| `edwards25519_scalarmulbase` | `edwards25519_scalarmulbase`: `EDWARDS25519_SCALARMULBASE_SUBROUTINE_SAFE` | `edwards25519_scalarmulbase_alt`: `EDWARDS25519_SCALARMULBASE_ALT_SUBROUTINE_SAFE` |
| `edwards25519_scalarmulbase_alt` | `edwards25519_scalarmulbase_alt`: `EDWARDS25519_SCALARMULBASE_ALT_SUBROUTINE_SAFE` | not imported |
| `edwards25519_scalarmuldouble` | not imported | `edwards25519_scalarmuldouble_alt`: `EDWARDS25519_SCALARMULDOUBLE_ALT_SUBROUTINE_SAFE` |
| `mldsa_caddq` | `mldsa_caddq`: `MLDSA_CADDQ_SUBROUTINE_SAFE` | `mldsa_caddq`: `MLDSA_CADDQ_SUBROUTINE_SAFE` |
| `mldsa_chknorm` | `mldsa_chknorm`: `MLDSA_CHKNORM_SUBROUTINE_SAFE` | `mldsa_chknorm`: `MLDSA_CHKNORM_SUBROUTINE_SAFE` |
| `mldsa_decompose_32` | `mldsa_decompose_32`: `MLDSA_DECOMPOSE_32_SUBROUTINE_SAFE` | `mldsa_decompose_32`: `MLDSA_DECOMPOSE_32_SUBROUTINE_SAFE` |
| `mldsa_decompose_88` | `mldsa_decompose_88`: `MLDSA_DECOMPOSE_88_SUBROUTINE_SAFE` | `mldsa_decompose_88`: `MLDSA_DECOMPOSE_88_SUBROUTINE_SAFE` |
| `mldsa_intt` | `mldsa_intt`: none | `mldsa_intt`: `MLDSA_INTT_SUBROUTINE_SAFE` |
| `mldsa_ntt` | `mldsa_ntt`: none | `mldsa_ntt`: `MLDSA_NTT_SUBROUTINE_SAFE` |
| `mldsa_nttunpack` | `mldsa_nttunpack`: `MLDSA_NTTUNPACK_SUBROUTINE_SAFE` | not imported |
| `mldsa_pointwise` | `mldsa_pointwise`: `MLDSA_POINTWISE_SUBROUTINE_SAFE` | `mldsa_pointwise`: `MLDSA_POINTWISE_SUBROUTINE_SAFE` |
| `mldsa_pointwise_acc_l4` | `mldsa_pointwise_acc_l4`: `MLDSA_POINTWISE_ACC_L4_SUBROUTINE_SAFE` | `mldsa_pointwise_acc_l4`: `MLDSA_POINTWISE_ACC_L4_SUBROUTINE_SAFE` |
| `mldsa_pointwise_acc_l5` | `mldsa_pointwise_acc_l5`: `MLDSA_POINTWISE_ACC_L5_SUBROUTINE_SAFE` | `mldsa_pointwise_acc_l5`: `MLDSA_POINTWISE_ACC_L5_SUBROUTINE_SAFE` |
| `mldsa_pointwise_acc_l7` | `mldsa_pointwise_acc_l7`: `MLDSA_POINTWISE_ACC_L7_SUBROUTINE_SAFE` | `mldsa_pointwise_acc_l7`: `MLDSA_POINTWISE_ACC_L7_SUBROUTINE_SAFE` |
| `mldsa_poly_use_hint_32` | `mldsa_poly_use_hint_32`: `MLDSA_POLY_USE_HINT_32_SUBROUTINE_SAFE` | `mldsa_poly_use_hint_32`: `MLDSA_USE_HINT_32_SUBROUTINE_SAFE` |
| `mldsa_poly_use_hint_88` | `mldsa_poly_use_hint_88`: `MLDSA_POLY_USE_HINT_88_SUBROUTINE_SAFE` | `mldsa_poly_use_hint_88`: `MLDSA_USE_HINT_88_SUBROUTINE_SAFE` |
| `mldsa_polyz_unpack_17` | `mldsa_polyz_unpack_17`: `MLDSA_POLYZ_UNPACK_17_SUBROUTINE_SAFE` | `mldsa_polyz_unpack_17`: `MLDSA_POLYZ_UNPACK_17_SUBROUTINE_SAFE` |
| `mldsa_polyz_unpack_19` | `mldsa_polyz_unpack_19`: `MLDSA_POLYZ_UNPACK_19_SUBROUTINE_SAFE` | `mldsa_polyz_unpack_19`: `MLDSA_POLYZ_UNPACK_19_SUBROUTINE_SAFE` |
| `mldsa_reduce` | `mldsa_reduce`: none | not imported |
| `mldsa_rej_uniform_eta2_vartime` | `mldsa_rej_uniform_eta2_VARIABLE_TIME`: `MLDSA_REJ_UNIFORM_ETA2_SUBROUTINE_SAFE` | `mldsa_rej_uniform_eta2_VARIABLE_TIME`: `MLDSA_REJ_UNIFORM_ETA2_SUBROUTINE_SAFE` |
| `mldsa_rej_uniform_eta4_vartime` | `mldsa_rej_uniform_eta4_VARIABLE_TIME`: `MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_SAFE` | `mldsa_rej_uniform_eta4_VARIABLE_TIME`: `MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_SAFE` |
| `mldsa_rej_uniform_vartime` | `mldsa_rej_uniform_VARIABLE_TIME`: `MLDSA_REJ_UNIFORM_SUBROUTINE_SAFE` | `mldsa_rej_uniform_VARIABLE_TIME`: `MLDSA_REJ_UNIFORM_SUBROUTINE_SAFE` |
| `mlkem_basemul_k2` | `mlkem_basemul_k2`: none | `mlkem_basemul_k2`: `MLKEM_BASEMUL_K2_SUBROUTINE_SAFE` |
| `mlkem_basemul_k3` | `mlkem_basemul_k3`: none | `mlkem_basemul_k3`: `MLKEM_BASEMUL_K3_SUBROUTINE_SAFE` |
| `mlkem_basemul_k4` | `mlkem_basemul_k4`: none | `mlkem_basemul_k4`: `MLKEM_BASEMUL_K4_SUBROUTINE_SAFE` |
| `mlkem_frombytes` | `mlkem_frombytes`: none | not imported |
| `mlkem_intt` | `mlkem_intt`: none | `mlkem_intt`: `MLKEM_INTT_SUBROUTINE_SAFE` |
| `mlkem_mulcache_compute` | `mlkem_mulcache_compute`: none | `mlkem_mulcache_compute`: `MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE` |
| `mlkem_ntt` | `mlkem_ntt`: none | `mlkem_ntt`: `MLKEM_NTT_SUBROUTINE_SAFE` |
| `mlkem_reduce` | `mlkem_reduce`: `MLKEM_REDUCE_SUBROUTINE_SAFE` | `mlkem_reduce`: `MLKEM_REDUCE_SUBROUTINE_SAFE` |
| `mlkem_rej_uniform_vartime` | `mlkem_rej_uniform_VARIABLE_TIME`: `MLKEM_REJ_UNIFORM_SUBROUTINE_SAFE` | `mlkem_rej_uniform_VARIABLE_TIME`: `MLKEM_REJ_UNIFORM_SUBROUTINE_SAFE` |
| `mlkem_tobytes` | `mlkem_tobytes`: none | `mlkem_tobytes`: `MLKEM_TOBYTES_SUBROUTINE_SAFE` |
| `mlkem_tomont` | `mlkem_tomont`: none | `mlkem_tomont`: `MLKEM_TOMONT_SUBROUTINE_SAFE` |
| `mlkem_unpack` | `mlkem_unpack`: none | not imported |
| `p256_montjadd` | `p256_montjadd`: `P256_MONTJADD_SUBROUTINE_SAFE` | `p256_montjadd_alt`: `P256_MONTJADD_ALT_SUBROUTINE_SAFE` |
| `p256_montjadd_alt` | `p256_montjadd_alt`: `P256_MONTJADD_ALT_SUBROUTINE_SAFE` | not imported |
| `p256_montjdouble` | `p256_montjdouble`: `P256_MONTJDOUBLE_SUBROUTINE_SAFE` | `p256_montjdouble_alt`: `P256_MONTJDOUBLE_ALT_SUBROUTINE_SAFE` |
| `p256_montjdouble_alt` | `p256_montjdouble_alt`: `P256_MONTJDOUBLE_ALT_SUBROUTINE_SAFE` | not imported |
| `p256_montjmixadd` | `p256_montjmixadd`: none | `p256_montjmixadd_alt`: none |
| `p256_montjmixadd_alt` | `p256_montjmixadd_alt`: none | not imported |
| `p256_scalarmul` | `p256_scalarmul`: none | `p256_scalarmul_alt`: none |
| `p256_scalarmul_alt` | `p256_scalarmul_alt`: none | not imported |
| `p256_scalarmulbase` | not imported | `p256_scalarmulbase_alt`: none |
| `p384_montjadd` | `p384_montjadd`: `P384_MONTJADD_SUBROUTINE_SAFE` | `p384_montjadd_alt`: `P384_MONTJADD_ALT_SUBROUTINE_SAFE` |
| `p384_montjadd_alt` | `p384_montjadd_alt`: `P384_MONTJADD_ALT_SUBROUTINE_SAFE` | not imported |
| `p384_montjdouble` | `p384_montjdouble`: `P384_MONTJDOUBLE_SUBROUTINE_SAFE` | `p384_montjdouble_alt`: `P384_MONTJDOUBLE_ALT_SUBROUTINE_SAFE` |
| `p384_montjdouble_alt` | `p384_montjdouble_alt`: `P384_MONTJDOUBLE_ALT_SUBROUTINE_SAFE` | not imported |
| `p384_montjmixadd` | `p384_montjmixadd`: none | `p384_montjmixadd_alt`: none |
| `p384_montjmixadd_alt` | `p384_montjmixadd_alt`: none | not imported |
| `p384_montjscalarmul` | `p384_montjscalarmul`: `P384_MONTJSCALARMUL_SUBROUTINE_SAFE` | `p384_montjscalarmul_alt`: `P384_MONTJSCALARMUL_ALT_SUBROUTINE_SAFE` |
| `p384_montjscalarmul_alt` | `p384_montjscalarmul_alt`: `P384_MONTJSCALARMUL_ALT_SUBROUTINE_SAFE` | not imported |
| `p521_jadd` | `p521_jadd`: `P521_JADD_SUBROUTINE_SAFE` | `p521_jadd_alt`: none |
| `p521_jadd_alt` | `p521_jadd_alt`: `P521_JADD_ALT_SUBROUTINE_SAFE` | not imported |
| `p521_jdouble` | `p521_jdouble`: `P521_JDOUBLE_SUBROUTINE_SAFE` | `p521_jdouble_alt`: `P521_JDOUBLE_ALT_SUBROUTINE_SAFE` |
| `p521_jdouble_alt` | `p521_jdouble_alt`: `P521_JDOUBLE_ALT_SUBROUTINE_SAFE` | not imported |
| `p521_jmixadd` | `p521_jmixadd`: none | `p521_jmixadd_alt`: none |
| `p521_jmixadd_alt` | `p521_jmixadd_alt`: none | not imported |
| `p521_jscalarmul` | `p521_jscalarmul`: `P521_JSCALARMUL_SUBROUTINE_SAFE` | `p521_jscalarmul_alt`: `P521_JSCALARMUL_ALT_SUBROUTINE_SAFE` |
| `p521_jscalarmul_alt` | `p521_jscalarmul_alt`: `P521_JSCALARMUL_ALT_SUBROUTINE_SAFE` | not imported |
| `sha3_keccak2_f1600` | not imported | `sha3_keccak2_f1600`: `SHA3_KECCAK2_F1600_SUBROUTINE_SAFE` |
| `sha3_keccak4_f1600_alt::sha3_keccak4_f1600` | `sha3_keccak4_f1600_alt`: none | not imported |
| `sha3_keccak_f1600` | `sha3_keccak_f1600`: none | `sha3_keccak_f1600`: `SHA3_KECCAK_F1600_SUBROUTINE_SAFE` |
| `sha3_keccak_f1600_alt::sha3_keccak_f1600` | not imported | `sha3_keccak_f1600_alt`: `SHA3_KECCAK_F1600_ALT_SUBROUTINE_SAFE` |
<!-- end admin/prove-bytes inventory -->

## Implementation details

### RSA
On x86_64 and aarch64, the Montgomery products are mostly aws-lc's, and
s2n-bignum provides the rest of the arithmetic, under the exponentiation
described below. x86_64 runs aws-lc's Montgomery multiplication as aws-lc's
`bn_mul_mont` picks it (`bn_mul4x_mont` for moduli whose width in 64-bit words
is a multiple of four, `bn_sqr8x_mont` for squaring a multiple of eight, each
by `mulx` with ADX, and `bn_mul_mont_nohw` for other widths), other than
1024- and 2048-bit moduli on CPUs with ADX, where s2n-bignum's Karatsuba
routines are as fast or faster, and the RSAZ paths below. aarch64 runs
aws-lc's `bn_mul_mont`, which picks its own squaring or 4x routine by the
width, at every size: on a Neoverse-N2 it measured 1.15 to 2 times as fast as
s2n-bignum's generic routines, and faster than its Karatsuba routines for
1024- and 2048-bit moduli.
armv7 runs the same exponentiation over aws-lc's 32-bit ARM `bn_mul_mont`
routines as aws-lc picks them (`bn_mul8x_mont_neon` with NEON for moduli whose
width in 32-bit words is a multiple of eight, and `bn_mul_mont_nohw`
otherwise), and the rest of the arithmetic in rind's portable Rust. The
portable backend runs it all in that Rust, over 64-bit limbs on 64-bit
targets and 32-bit ones elsewhere: its Montgomery products below 16 limbs by
rind's loop (Koç, Acar, and Kaliski's CIOS method), and wider ones and its
squarings by forming the product, each square's cross products once, then
reducing it, adding two rows a pass in two carry chains. Products split by
Karatsuba's method from 32 limbs and squares from 64, as aws-lc's C does
from 16 words. RSA signing and verification at 2048 to 8192 bits measured
at 0.85 to 0.97× aws-lc's C time without assembly on x86_64.
On x86_64 CPUs with AVX2 but without ADX, the private operation's exponentiation modulo each 1024-bit
prime of RSA-2048 runs aws-lc's RSAZ, as aws-lc does there: Montgomery
products on AVX2 over 29-bit limbs, and a 5-bit fixed window whose table
entry is gathered by masking all 32 entries. Otherwise x86_64 runs aws-lc's
5-bit window, as `BN_mod_exp_mont_consttime` does, gathering each entry by
masking all 32 entries with AVX2, and otherwise by s2n-bignum's verified
routine, which reads every entry. For moduli of a
multiple of 512 bits other than 1024 and 2048 bits with ADX, it runs aws-lc's
`bn_power5` instead: five squarings and the product by an entry gathered by
masking all 32, in one call.
On x86_64 CPUs with AVX-512 IFMA (with F, VL, BMI2, and ADX), RSA runs
[verified-garbage]'s routines where they measured faster than rind's at
every size they cover, under rind's key types, checks, padding, and fault
check. The public operation of a 2048-, 3072-, or 4096-bit modulus with
e = 65537 runs its almost Montgomery products over 52-bit limbs, at 0.49 to
0.56× rind's time on Zen 4; other moduli and exponents keep rind's, as VG
falls back to 64-bit products there that measured 1.15 to 1.54× slower at
2056 bits. Both exponentiations of the CRT for 1024- or 2048-bit primes run
at once by its CRT, at 0.96 and 0.98× the dual RSAZ's time on Zen 4, about
0.9 on Zen 5, and 0.74 and 0.96 on a Granite Rapids Xeon, by a fixed window
whose entries are gathered by masking all of them. On CPUs with AVX512_FP16
(Intel's since Sapphire Rapids) it takes its form for two 512-bit
multipliers, as VG's own dispatch does, which also runs 1536-bit primes, at
0.92× on that Xeon. Its other form measured 1.2 to 1.5× slower there on Zen
5, so elsewhere a 3072-bit key's CRT runs aws-lc's dual RSAZ, as aws-lc's
`BN_mod_exp_mont_consttime_x2` does there: almost Montgomery
products on 256-bit vectors over 52-bit limbs, two moduli at a time, and a
5-bit fixed window whose table entries are gathered by masking all 32.
The dual RSAZ also runs the keys of 2048-bit-class primes whose modulus has
63 words (3969 to 4032 bits), which neither form of VG's CRT takes.
Valgrind runs no AVX-512, so `admin/ct-sde` checks each of these under Intel
SDE instead.

The RSA private operation always uses the CRT optimisation.

On aarch64 and armv7, modular exponentiation uses a 5-bit fixed exponent window, as aws-lc's does,
and the term is selected by the exponent bits from the table of base powers in a side-channel-free way.

On every architecture, the private operation is always followed by the public operation to verify the result
(and the result compared in a side-channel-free way).

RSA signs and verifies with PKCS#1 v1.5 and PSS, and encrypts with OAEP on
SHA-1, SHA-256, SHA-384, or SHA-512.  Private keys have 2048- to 8192-bit
moduli; verification also takes 1024-bit moduli and SHA-1, but only under
`rsa::verify::legacy`.  Every key refuses a public exponent that is
even, 1, or over 33 bits, and a private key whose components disagree is
refused when it loads, as aws-lc's `RSA_check_key` does.  Public keys load
from PKCS#1 `RSAPublicKey` or `SubjectPublicKeyInfo` DER, or from their
modulus and exponent.  Each OAEP key is bound to one hash.  OAEP decryption is
constant time through its padding check, and fails every malformed
ciphertext with the same error, so it is no Manger oracle.  PKCS#1 v1.5
encryption, which invites padding-oracle attacks, is refused.

RSA blind signatures (RFC 9474) take no arithmetic of their own: a client
blinds a message's RSASSA-PSS encoding by the public operation on a random
blind and a Montgomery multiplication, the server signs it by the private
operation above, checked against its public key, and the client unblinds the
reply by the blind's inverse, from `bignum_modinv`.  Rather than
RSASSA-PSS-VERIFY, which would branch on what a malicious reply unblinds to
(1 unblinds to the inverse itself), the client checks in constant time that
the result's public operation gives the very encoding it blinded.  Blinding
and unblinding run in constant time in the message, its prefix and salt, and
the blind, revealing only which candidate blinds rejection sampling discards
and whether the reply was good.

RSA key generation is supported for five fixed key sizes between 2048-8192-bits.
All generated keys have e = 0x10001 and, as in aws-lc, d reduced mod
lcm(p - 1, q - 1).  Generation runs in constant time in the primes, revealing
only which candidates it discards.

### ECC
On x86_64 and aarch64, all ECC field and scalar arithmetic are provided by
s2n-bignum, except P256's on x86_64 where aws-lc's is named below, and
Ed25519 verification's on x86_64 CPUs with AVX2 but without ADX, which runs
curve25519-dalek's AVX2 backend. x86_64's Ed25519 verification splits `k`
by the extended Euclidean algorithm on `8L` and `k`, stopped halfway, then
sums four multiples by Straus's method: width-5 non-adjacent forms of the
two half-size scalars over tables of `-R`'s and `±A`'s odd multiples, and
width-8 forms of `v S`'s two 128-bit halves over 10 KiB static tables each
of `B`'s and `[2^128]B`'s, so the loop runs about 128 doublings. The rest
of this section describes those backends.

On x86_64 CPUs with AVX-512 IFMA (with F, VL, AVX2, BMI1, BMI2, and ADX),
X25519 and Ed25519 run [verified-garbage]'s routines instead, its variants
for CPUs without the SHA-512 instructions, as its own dispatch picks on
every CPU with IFMA measured so far. Each is a whole RFC 7748 or RFC 8032
operation, Ed25519's SHA-512 included, since VG's lower routines are
internal ones without a contract of their own. rind keeps its key types,
loading, and checks, so it still refuses small-order Ed25519 public keys,
which VG accepts, and decodes a public key when it loads, though VG decodes
it again to verify. VG's verification checks what rind's does: canonical
encodings, `S < L`, and the equation without the cofactor, for `k` reduced
modulo `L`. On a Zen 4 EPYC 9V74, VG took 0.52-0.67 of rind's time for
X25519, and 0.66, 0.68, and 0.55 for Ed25519 key generation, signing, and
verification, in [run 43531095881]; on Zen 5 (a Ryzen 9 9950X), against
the code it replaced, 0.62-0.72 for X25519 and 0.61, 0.67, and 0.85 for
Ed25519, in [kixel-ai/rind#845](https://github.com/kixel-ai/rind/pull/845); and on a
Xeon 6975P-C, 0.66-0.72 for X25519 and 0.69, 0.66, and 0.90 for Ed25519,
in [run 44171095372] against [run 43881997679] before the switch. Without
IFMA, VG lost at some operation on every CPU measured: on a Zen 4 EPYC 9V74
whose VM hid AVX-512, 0.92-0.97 but 1.07 for verification, in [run
44169300257]; 1.10-1.77 on that run's tiers that deny ADX or AVX2; 1.09 for
signing on a Zen 3 Ryzen 9 5900XT; and up to 1.17 for verification on Arrow
Lake, whose SHA-512 instructions VG also runs, though under load.

Where s2n-bignum ships a routine in two verified variants, aarch64 runs the
scalar `_alt` one under the plain name: on Apple's M1 and M4 and on Neoverse
N2 it runs every curve routine rind uses in 50-98% of the time of the
other, which mixes in SIMD multiplies.

P256 base point multiplication on x86_64 runs aws-lc's algorithm: 7-bit Booth
windows over 37 rows of 64 affine points (a 152KB constant table), each row
scanned whole by rind's constant-time Rust select and added by aws-lc's mixed
addition, `ecp_nistz256_point_add_affine`, with `mulq` or with BMI2 and ADX,
in the order aws-lc's `ecp_nistz256_point_mul_base` runs them. On
aarch64 it is s2n-bignum's `p256_scalarmulbase`, over 6-bit Booth windows and
a table of each window's 32 multiples (an 88KB constant table). Variable
point multiplication is s2n-bignum's `p256_scalarmul` on both, whose proof
covers the conversion back to affine coordinates.

armv7 runs the aarch64 algorithms for P256 in portable Rust, over
fiat-crypto's field and scalar arithmetic, except its Montgomery
multiplication and squaring, which are rind's. LLVM compiles fiat-crypto's
32-bit multiplication to save and restore the one carry flag 171 times a
call, between its interleaved carry chains; rind's carry in 64-bit
accumulators (`umaal`) instead, in 560 instructions run to fiat-crypto's
1,375. fiat-crypto cannot generate an unsaturated P256, as it does P521:
its bounds checks fail at every 32-bit limb count from 9 to 16. armv7's
P384 runs rind's Montgomery multiplication and squaring the same way, in
1,151 instructions to fiat-crypto's 2,254, over fiat-crypto's other field
and scalar arithmetic. The portable backend runs the same on 32-bit
targets, and on 64-bit ones over fiat-crypto's 64-bit arithmetic whole, its
multiplication included.

P-256 runs [verified-garbage]'s routines instead where they measured faster
than rind's at every size, each a whole operation on encoded keys under
rind's key types and glue: ECDH, which validates the peer's point again, and
ECDSA verification of the hash's leftmost 256 bits, on x86_64 with BMI2 and
ADX (and AVX and AVX2), over 52-bit limbs with AVX-512 IFMA, and on every
aarch64 CPU; and a public key's derivation on aarch64, on Intel, and with
AVX-512 IFMA. In CI, rind's time over aws-lc-rs's fell to 0.87 of what it
was for ECDH and to 0.66 to 0.80 for verification on x86_64 with IFMA, and
to 0.85 to 0.97 for every P-256 row on Neoverse N2. On an Arrow Lake core a public key's derivation took 0.88 of rind's time and
0.92 on Zen 5, but 1.02 to 1.06 on Zen 3, so AMD CPUs without IFMA keep
rind's for it. VG signs only by RFC 6979, so signing keeps rind's hedged
nonce and arithmetic and takes VG's derivation only for the nonce's point.
Without ADX VG measured slower, so rind's code runs there. rind claims no ✓
for VG's P-256 until [its quest](quest/m2/verified-garbage/p256-proof.md)
imports VG's theorems.

P384 base point multiplication uses a comb of 20 tables of 16 affine points
(a 30KB constant table) over 5-bit Booth windows, as aws-lc does. Variable
point multiplication is s2n-bignum's `p384_montjscalarmul`.

P521's prime is a Mersenne prime, so its field arithmetic is direct rather
than Montgomery's. Base point multiplication uses a comb of 27 tables of 16
affine points (a 62KB constant table) over 5-bit Booth windows, as aws-lc
does. Variable point multiplication is s2n-bignum's `p521_jscalarmul`.
s2n-bignum's P521 point addition requires points that are not at infinity,
equal, or opposite, so the comb keeps to that, selecting around the cases
it reaches.

ECDSA verification computes `u1 G + u2 Q` in one chain of doublings, as
aws-lc does, adding terms from width-5 non-adjacent forms of the public
scalars: `u2`'s over the public key's odd multiples, computed when the key is
parsed and made affine by one batched inversion, and `u1`'s over the first
row of the base point table, at width 6 for P256, as its aarch64 row holds 32
multiples, so every addition is a mixed one. A key's second verification
also builds 17Q to 31Q, so that `u2`'s digits widen to 6 from then on: a key
verified once never pays for them. s2n-bignum's point
additions are proven only for unequal points, so each addition first
compares x's and settles equal or opposite points by cases. The portable
backend's P521 runs the whole chain in fiat-crypto's limbs, rather than
converting each coordinate to and from words at every point routine, and
reads the x's difference from the addition's own first steps. Each curve
then checks `r` against `X / Z²` as `r Z² = X`, and `(r + n) Z² = X` when
`r + n < p`, without an inversion.
Those checks cost a key parsed and verified once, as TLS does with each
certificate key, about 5-6% against verifying without them (aarch64 and
x86_64 P-256 runs 41907443804 and 41907448202); keys verified more than once
are faster than before.

ECDSA follows RFC6979 for generation of `k`, but adds additional non-critical random input.
We do this to avoid the theoretical fragility of RFC6979 under fault conditions.
This is allowed for by RFC6979, and the HMAC-DRBG that it builds on.
The code is structured such that we pass the RFC6979 test vectors.

The code which selects a term from a table of points is non-verified,
and is written in AVX2, SSE2, or Neon intrinsics, or for P256 on x86_64 is
aws-lc's SSE2 and AVX2 assembly, or on armv7 is portable Rust. aarch64's P256
base point multiplication is the exception: its selection is inside
s2n-bignum's verified `p256_scalarmulbase`.

On x86_64 and aarch64, X25519 directly uses the s2n-bignum implementation,
but on x86_64 CPUs with AVX-512 IFMA, which run verified-garbage's (see above).

ECVRF (RFC 9381) is rind's, over the curves' code above: on edwards25519, the
ristretto255 code's constant-time variable-point multiplication and
s2n-bignum's base point multiplication and decoding, or curve25519-dalek's on
armv7 and portable; on P256, the ECDH and ECDSA multiplications, and RFC6979
over the HMAC-DRBG for the nonce, with no added randomness, as the suite's
test vectors require. Proving runs in constant time in the key and the nonce.
Verification multiplies by the proof's scalars in constant time too on
edwards25519, where it is public data, as no variable-time multiplication of
an arbitrary point is there to reuse; P256's computes `s G - c Y` as ECDSA
verification does. Try-and-increment's loop runs in time that depends on the
input, as RFC 9381 notes.

The OPRFs (RFC 9497) are rind's too, over the same code: ristretto255's
constant-time multiplications and RFC 9496 map, or curve25519-dalek's on
armv7 and portable, and the NIST curves' ECDH multiplications and RFC 9380
hash-to-curve, with `expand_message_xmd` over the suite's SHA-2 for each
hash to a scalar. Blinding, evaluation, proving, and finalization run in
constant time in the input, the blind, the key, and the proof's nonce.
Verifying a DLEQ proof handles public data only: ristretto255's still
multiplies in constant time, as with ECVRF on edwards25519, and the NIST
curves' compute `s G + c Y` as ECDSA verification does, and their other
sums from constant-time products. The suites' vectors and the `voprf` crate
cover the composition; nothing in it is proven.

FROST (RFC 9591) is rind's as well, over the same code: edwards25519's and
ristretto255's constant-time multiplications, or curve25519-dalek's on armv7
and portable, and P-256's ECDH base point multiplication and RFC 9380
`hash_to_field`. Dealing, nonce generation, and signing run in constant time
in the dealer's polynomial, the shares, and the nonces. Binding factors, the
group commitment, and verifying a share or a signature handle public data:
edwards25519's and ristretto255's still multiply in constant time, and P-256
computes its sums as ECDSA verification does. A FROST(Ed25519, SHA-512)
signature verifies through rind's Ed25519. The suites' vectors and the Zcash
Foundation's `frost-*` crates cover the composition; nothing in it is proven.

### ML-KEM
On aarch64, and on x86_64 CPUs with AVX2, the core polynomial arithmetic -- the NTT, inverse NTT, base multiplication
and reduction -- is provided by s2n-bignum (contributed by the mlkem-native
developers), with a base multiplication routine for each rank: 2, 3, and 4
for ML-KEM-512, ML-KEM-768, and ML-KEM-1024. The surrounding FIPS-203
construction (key generation, encapsulation and decapsulation) is written in
Rust, generic over the parameter set. With AVX2, ciphertext compression at
each width (4, 5, 10, and 11 bits) runs mlkem-native's AVX2 assembly;
decompression, and ML-KEM-512's centered binomial sampling with eta 3, are
Rust on every backend.

x86_64 CPUs without AVX2 run the same construction over a Rust port of
mlkem-native's portable C arithmetic instead, in natural coefficient order as
aarch64 keeps it, and Keccak-f four states one at a time, chosen once per
process. It measured 1.3x faster than libcrux's portable ML-KEM for key
generation and encapsulation there, and 2x for decapsulation.

armv7 runs the same construction and arithmetic, with [OpenSSL]'s Keccak-f:
NEON where the CPU has it, and integer code on bit-interleaved lanes
otherwise. Keccak-f dominates ML-KEM there, and compiled code spills its
state. With NEON it measured 1.5x faster than libcrux's portable ML-KEM for
key generation and encapsulation, and 2.8x for decapsulation. Without NEON,
under qemu, it ran key generation and encapsulation in 1.3x fewer
instructions. The portable backend runs it with rind's Keccak-f, proven in
[`proofs/`](proofs/README.md).

ML-KEM-768 runs [verified-garbage]'s routines instead where they measured
faster than rind's at every step they cover: each is a whole FIPS 203
operation, hashing included, under rind's key types and glue. Its
encapsulation, and the encapsulation key check that parsing a key runs, take
VG's on every x86_64 CPU and on aarch64 with the SHA-3 instructions, at
0.66-0.87x rind's time. Key generation and decapsulation take VG's only on
x86_64 with AVX-512 (F, BW, and VL), at 0.81x and 0.96x; elsewhere VG's
decapsulation measured 1.17-1.25x slower, and a key pair decapsulates with
the code that generated it, so both stay rind's. On aarch64 without the SHA-3
instructions VG measured 1.35x slower or more at every step, so rind's runs
there. A VG routine reports when a `SampleNTT` reaches its loop bound, with
probability below 2^-261; rind then runs its own arithmetic for that call.

Compression and decompression are division-free, avoiding the variable-time
division behind the KyberSlash attacks.

For sampling, which is a significant factor in ML-KEM performance, we
have some different options depending on CPU features:

- We have a `SampleNTT()` which does 8-wide Keccak-f permutation followed by
  rejection sampling using AVX-512 (F, BW, VL, VBMI, VBMI2) on x86-64, for
  ML-KEM-1024. ML-KEM-512's four polynomials never fill a batch of eight.
  ML-KEM-768's nine could, but rind skips it for ML-KEM-768, including when
  it falls back from verified-garbage's routines, and samples eight four at
  a time and the ninth alone. This is Graviola's, and not verified.
- We have s2n-bignum's verified 4-wide Keccak-f using AVX2 on x86-64, and its
  single-state Keccak-f otherwise.
- We have s2n-bignum's verified 2-wide Keccak-f using Neon+SHA3 on Apple
  targets.
- We have s2n-bignum's verified single-state Keccak-f on aarch64, using the
  SHA3 instructions on Apple targets, whose cores run them on every SIMD
  unit, and scalar code on others. On Neoverse N2 the scalar code measured 2.1x faster
  than the SHA3 instructions for SHA-3, and 1.1-1.3x for ML-KEM and ML-DSA,
  which run it one state at a time; mlkem-native and verified-garbage make
  the same choice.
- We have OpenSSL's Keccak-f, on NEON or bit-interleaved in integer code, on
  armv7.
- We have rind's Keccak-f, proven in [`proofs/`](proofs/README.md), one state
  at a time, on the portable backend.

### ML-DSA
ML-DSA-44, ML-DSA-65, and ML-DSA-87 share one FIPS 204 construction (key
generation, signing, verification, and the key and signature encodings): a
Rust port of [mldsa-native]'s C. On aarch64, and on x86_64 CPUs with AVX2,
its polynomial arithmetic and rejection sampling run s2n-bignum's verified
routines, contributed by the mldsa-native developers: the NTT and its
inverse, pointwise multiplication, reduction, decomposition, hints, norm
checks, and unpacking.

x86_64 CPUs without AVX2, armv7, and the portable backend run a Rust port of
mldsa-native's portable C arithmetic instead. Its NTT walks each layer
through split slices, which leave its butterflies without bounds checks;
indexing as the C does left portable signing 1.07-1.12x slower than
aws-lc-rs. Keccak-f, which expands the matrix and samples the secrets, the
mask, and the challenge, runs as ML-KEM's does (see
[ML-KEM](#ml-kem)), four states at a time where the CPU allows.

Signing declassifies which attempt it accepts, and why it rejects the
others, as mldsa-native does: FIPS 204's security argument makes them
public.

On an AMD Ryzen 9 9950X shared with other jobs, so noisy, rind took
0.64-0.75x aws-lc-rs's time with AVX2, 0.82-0.91x without it, and
0.83-0.92x on the portable backend, for key generation, signing, and
verification at each parameter set. libcrux's, RustCrypto's, and
OpenSSL's ML-DSA were slower than aws-lc-rs's with AVX2, and libcrux's
portable ML-DSA was no faster than aws-lc-rs without assembly.

### SLH-DSA
SLH-DSA's twelve FIPS 205 parameter sets share one construction, generic
over the set: a Rust port of the [SPHINCS+] team's FIPS 205 code, with its
AVX2 builds' multi-lane tree hashing (`treehashx4` and `treehashx8`)
generalised over the lane count, so that each tree's leaves, WOTS+ chains,
and FORS nodes hash several at a time on every CPU.

- The SHAKE sets hash four lanes at once on rind's four-way Keccak-f, as
  ML-KEM does (see [ML-KEM-768](#ml-kem-768)), absorbing `PK.seed`, the
  address, and the message where they lie, without copying them together.
  A single lane, as verification's paths up each tree hash, runs one state.
- The SHA-2 sets hash eight lanes, each continuing SHA-256 from the state
  after the block `PK.seed || 0`, which every F, PRF, and category 1 H and
  `T_l` start with. With SHA-NI they run one at a time, which on an Arrow
  Lake core was 2.6x faster than [SPHINCS+]'s eight-way AVX2 code; without
  SHA-NI but with AVX2 that code runs, about 4x faster than one at a time.
  Categories 3 and 5 hash H and `T_l` with SHA-512, one at a time.

A signature reveals its randomiser `R`, and with it the indices the message
digest picks and each tree root the layers above sign, so signing
declassifies them as it derives them. What stays secret is `SK.seed` and
`SK.prf`, and the chain values and leaves derived from them, which only
constant-time hashes touch.

On an Intel Core Ultra 7 270K Plus (Arrow Lake) shared with other jobs, rind
took 0.3-0.57x the time of the [SPHINCS+] team's AVX2 C, the fastest other
code measured, for the SHA-2 sets' key generation, signing, and
verification, and 0.57-1.2x for the SHAKE sets', faster at key generation
and 128f signing and slower at the rest, as above. OpenSSL 3.5's SLH-DSA took
2.1-3.8x rind's time, RustCrypto's `slh-dsa` 1.8-5.4x, and integritychain's
`fips205` 2.6-5.4x.

### Symmetric cryptography
SHA1 and SHA256 have straightforward implementations using hashing intrinsics
(aka "SHA-NI" on x86_64, "sha" extension on aarch64), except that aarch64 runs
aws-lc's SHA256 assembly for those instructions: it keeps a register copy off
each round's dependency chain, where LLVM's code for the intrinsics puts one
on it, and x86_64 runs LLVM's code for its SHA256 intrinsics frozen into
inline assembly, so that a proof can be about the bytes it runs, with the
last block's padding in Rust. Without SHA-NI, x86_64
selects at runtime an AVX2 message schedule with scalar rounds for SHA1, as
aws-lc does, and for SHA256 runs OpenSSL's AVX2 routine, which aws-lc leaves
out: 1.12x faster than aws-lc's AVX routine on an i7-8700 and 1.13x on Arrow
Lake, and 1.17x faster than the Rust AVX2 port it replaces on the i7-8700.
Without AVX2, both run aws-lc's AVX routines on Intel and its SSSE3 ones
elsewhere, as aws-lc picks; they are
2.2x (SHA256) and 1.7x (SHA1) faster than the pure Rust ones on Intel.
Without SSSE3 too, both run aws-lc's integer routines, as aws-lc does: 2.2x
(SHA256) and 1.25x (SHA1) faster than the pure Rust ones, and 1.3-1.5x
faster than HACL*'s SHA256.
aarch64 without the crypto extension runs aws-lc's
scalar SHA1 and SHA256 assembly. 32-bit `arm` runs aws-lc's SHA1 assembly:
the crypto extension where the CPU has it, NEON where it has NEON, and the
integer routine otherwise. Its SHA256 runs aws-lc's crypto extension routine
where the CPU has it, and rind's Rust otherwise.

SHA384, SHA512, and SHA512/256 run aws-lc's assembly everywhere but on
x86_64 CPUs with AVX2, which run OpenSSL's: its routine for the SHA512
instructions where the CPU has them, 5.4x faster than aws-lc's AVX routine on
Arrow Lake, and its AVX2 routine otherwise, which aws-lc leaves out: 1.18x
faster than aws-lc's AVX routine on an i7-8700 and 1.15x on Arrow Lake, and
1.47x faster than its scalar one on AMD's Zen 3. Without AVX2, aws-lc's AVX
routine runs on Intel and its scalar routine on other CPUs, as aws-lc picks:
the AVX routine is 1.1x faster than the scalar one on Intel, and 1.5x slower
on AMD's Zen. On aarch64, its routine for the SHA-512 instructions where the CPU
has them, and its scalar routine otherwise; 32-bit `arm` and the portable
backend run rind's own: the eighty rounds unrolled on a 64-bit pointer, and a
loop on a 32-bit one, which keeps the body inside a 16 KiB instruction cache.

PBKDF2 runs rind's loop over its HMAC, keyed once per secret, but on aarch64
with the crypto extension for HMAC-SHA1 and HMAC-SHA256, and with the SHA-512
instructions for HMAC-SHA384 and HMAC-SHA512, where it runs
[verified-garbage]'s routine, without a ✓ until rind imports VG's theorems
(see [Sources](#sources)). That routine is the whole of PBKDF2, keying HMAC
itself on every call, so a secret keeps HMAC's key, the secret or its hash,
for it, and `verify` derives the whole key before comparing. At 1000
iterations it took 0.90-0.93 of rind's loop's time on Neoverse N2 in [run
44171828157] and 0.82-0.85 on Apple M4. Without those instructions VG's
routine took 1.00-1.06 of rind's time on N2, so rind keeps its loop.

SHA3-256, SHA3-384, and SHA3-512 run Graviola's sponge over the Keccak-f
ML-KEM uses (see [ML-KEM](#ml-kem)), one state at a time.
[`proofs/`](proofs/README.md) proves the sponge, and ML-KEM's SHAKE calls,
against FIPS 202 down to s2n-bignum's Keccak-f routines on x86_64 and
aarch64, and the portable backend's Keccak-f against the spec those routines'
proofs state.

x86_64 decides once per process whether the CPU has AES-NI and PCLMULQDQ,
and SSSE3. Without the first two, as on Core 2 and Nehalem, AES and AES-CTR
run aws-lc's `vpaes-x86_64` assembly and GHASH its `ghash-ssse3-x86_64`,
composed into AES-GCM as aws-lc composes them, taking turns over 3 KB; both
modes measured level with aws-lc's. Without SSSE3 either, as on QEMU's
`qemu64`, they run Rust ports of the C aws-lc runs there: `aes_nohw.c`, which
bitslices eight blocks into SSE2 registers and computes the S-box as a
circuit, and `gcm_nohw.c`, which multiplies with integer multiplies of
operands masked to every fourth bit, so no carry reaches a bit it keeps.
Neither branches or indexes memory by a secret. Composed the same way,
AES-GCM and AES-CTR measured 0.82-0.92x aws-lc's time; libcrux's portable
AES-GCM measured 3-7x slower. With AES-NI and PCLMULQDQ, AES-CTR runs aws-lc's
`aes_hw_ctr32_encrypt_blocks`, 1.1-2x faster than rind's by-8 intrinsics at
every length, with or without AVX.

AES-GCM has a stitched by-8 AES-CTR and a by-8 GHASH, SSE-encoded on every
CPU: VEX encoding measured no faster with AVX, and without it, as on Westmere
and the Goldmont and Tremont Atoms, this is 1.02-1.28x faster than aws-lc's
SSE `aesni-x86_64` and `ghash-x86_64` routines. With AVX and MOVBE but no
VAES, as from Haswell through Comet Lake and on Zen 1 and 2, [HACL\*]'s
Vale AES-GCM runs the AEAD: its counter block, and a port of OpenSSL's
`aesni_gcm`, which interleaves AES-CTR and GHASH six blocks at a time from
288 bytes to encrypt and 96 to decrypt, then takes the rest a block at a time
and checks the tag. Seals under 129 bytes run the by-8 path instead, as Vale's
measured 0.94-1.19x its time there on Coffee Lake (medians 1.04-1.06x). rind computes the round keys and GHASH key powers itself,
in the layout Vale's proof assumes, since Vale's own setup measured twice as
slow, and `proofs/` proves them and the Rust around Vale's routines end to
end. Vale's proof stops at 2^32 bytes of message or AAD, so longer ones run
the by-8 code, as do those short seals, IVs other than 96 bits, and the
opening of truncated tags, whose tag check Vale's routine does not take.
`proofs/` proves the by-8 code against Vale's AES-GCM spec without that
bound, for 96-bit IVs and full tags, with AES-128 and AES-256. Every 256- and 512-bit kernel rind runs ends with
`vzeroupper`, so SSE code after one pays no AVX-SSE transition or false
dependency. There is also an optional AVX-512 by-16 AES-CTR
and GHASH.  It uses dynamic CPU feature detection, so AVX-512 is not required at runtime.
On cores with VAES, BoringSSL's kernels, which interleave AES-CTR and GHASH, take
long messages: its 512-bit kernel from 2 KB where the CPU has AVX-512 (the by-16
path is quicker below that), and its 256-bit kernel from 256 bytes otherwise.
Below 256 bytes, Vale's AES-GCM opens on VAES cores without AVX-512, where it
measured 0.83-1.09x the by-8 path's time on Zen 3 (median 0.95x), and
0.74-1.06x on Arrow Lake's P-cores and 0.70-1.08x on its E-cores (medians
0.88x and 0.90x), under an AAD of a partial block, as QUIC's and TLS's are,
or of whole ones. Short seals there run the by-8 path, which Vale trailed on
both from 16 bytes up to 176. AVX-512 cores run the by-8 path for every short
message: Vale's opens measured 0.95-1.44x its time on Zen 5 (median 1.03x),
0.96-1.37x on Granite Rapids (median 1.07x), and 0.70-1.14x on Zen 4 (median
1.00x), and its seals lost on all three.
Vale's proof covers those short opens' kernel, but not the choice of it,
which [`proofs/`](proofs/README.md) proves only without VAES. On AVX-512
cores, `proofs/` proves the by-16 and by-8 paths below 2 KB, given the key
powers BoringSSL's setup computes, which nothing proves yet.
The key picks its kernel once, when it is made.

aarch64 decides once per process whether the CPU has the crypto extension.
With it, AES-GCM runs s2n-bignum's kernels, which interleave AES-CTR and GHASH
over whole blocks: by 8 on a core with SHA3, using its three-way XOR, as aws-lc
does on Apple and Neoverse V cores, and by 4 otherwise. They run in place,
which their theorems allow. Up to 15 blocks of AAD and message
sealed, or 31 opened, rind's own Rust runs instead: one pass that encrypts
every counter block and the tag's, and hashes every block with one reduction
per eight. It measured 0.41-0.97x the kernels' time on Neoverse N2 and
0.51-0.89x on Apple M1, gaining least near those limits. Its tests check it
against vpaes and NEON GHASH.

Without it, AES runs aws-lc's `vpaes-armv8`, Mike Hamburg's vector permutation
AES, whose S-box is NEON `tbl` lookups into registers, and GHASH runs aws-lc's
`ghash-neon-armv8`, which builds each product from NEON's 8-bit polynomial
multiplies; neither reads memory or branches by a secret. AES-GCM runs AES-CTR
and GHASH over each eight blocks in turn, as aws-lc composes them.

32-bit `arm` decides once per process from `AT_HWCAP2`: with the crypto
extension, AES and AES-GCM keys use aws-lc's `aesv8-armx` and `ghashv8-armx`
assembly, composed as aws-lc does on that architecture; without it, the
same `aes_nohw.c` port x86_64 runs without SSSE3, in its 32-bit
configuration, which bitslices two blocks into 32-bit words, and for AES-GCM a
port of aws-lc's `gcm_nohw.c` in its 32-bit configuration, composed the same
way. A key expands both once, when it is made, holding its round keys
bitsliced, and seals and opens in place. The portable backend always takes the
paths without the extension, and runs both ports in their 64-bit
configurations on 64-bit targets, four blocks into 64-bit words. On x86_64
under `--cfg rind_portable` they measured 0.18x the time of the libcrux
bitsliced block cipher they replaced for AES-GCM from 1200 bytes, and
0.93-1.03x aws-lc's time there, whose C bitslices eight blocks into SSE2
registers on that row; AES-CTR and CBC decryption measured 1.08-1.23x it.

AES-192 takes each of these paths with 12 rounds, but for three sources with
no AES-192: Vale's AES-GCM, so x86_64 runs the by-8 code where Vale would
run; s2n-bignum's aarch64 AES-GCM kernels, so aarch64 runs aws-lc's by-8
`aesv8_gcm_8x_enc_192` and `aesv8_gcm_8x_dec_192` past `short`'s lengths on a
core with SHA3, which aws-lc runs on Apple and Neoverse V cores, and AES-CTR
and GHASH in turn without it.
aws-lc's routines are not verified. Valgrind hides SHA3 from
`admin/ctgrind`, so `admin/ct-qemu` checks them, and the eight-way kernels,
under qemu-aarch64.
AES-NI and ARMv8 expand an AES-192 key six words per vector step, with the
SubWord the other sizes take, measured 0.88-0.94x aws-lc-rs's AES-GCM key
setup on Zen 3 and Neoverse N2; the bitsliced path runs aws-lc's schedule,
which keeps a window of a block and a half. Against aws-lc-rs, AES-192-GCM measured 0.43-0.57x on
Zen 3 with VAES and 0.44-1.03x without AVX2, as AES-128 did, 0.43-0.47x on
N2 at 32 bytes and 0.74-0.84x from 1200 bytes, where aws-lc runs its by-4
routine, and 0.90-1.02x on Apple M1 and 0.92-0.99x on M4 from 1200 bytes
with `rind::cpu::Dit::hold()` held, 1.01-1.21x without it.
AES-192-CTR and CBC measured as AES-128 did on each.

x86_64 CPUs with AVX2 run ChaCha20 from 256 bytes on [verified-garbage]'s
routines, its AVX-512 VL one where the CPU has AVX-512 VL and its AVX2 one
otherwise, with VG's ✓, whose theorems [`proofs/`](proofs/README.md)
restates as axioms (see [Sources](#sources)). It runs no slower than the
code it replaced at any length measured from 32 bytes to 16 KiB, and from
256 bytes took 0.54-0.97 of its time on Arrow Lake (AVX2) and 0.36-0.96 on
Zen 5 (AVX-512) in
[kixel-ai/rind#811](https://github.com/kixel-ai/rind/pull/811), and 0.43-0.62
at the benchmark's sizes from 1200 bytes on a Xeon 6975P in [run
43881997679]. Below 256 bytes, Graviola's two-block AVX2 kernel runs from
two blocks and HACL*'s verified rounds in general-purpose registers for one,
as QUIC header protection takes and as aws-lc runs its integer routine
there: VG's routines set up a 768-byte streaming state. VG's AVX2 routine
runs what follows its eight-block loop on narrower paths, which lost to the
kernel by up to 1.73x on Arrow Lake, so on either routine a remainder of 65
to 255 bytes after the last whole 512-byte group runs on the kernel too. Graviola's kernels compute even one block
as a single serial chain, which Zen 5's two-cycle vector latency doubles,
so header protection on them took 1.89 of aws-lc-rs's time on an EPYC 9V45
in [run 41585945720]. On HACL*'s rounds it takes 0.89 on an EPYC 9V74 (Zen
4) in [run 41678532920], against 0.83 on the kernels in [run 41657617706].
For one block, the kernels measured 1.05-1.3x faster than HACL*'s rounds on
Coffee Lake, Arrow Lake, and Zen 3, where HACL*'s rounds are within 10% of
aws-lc's integer routine.

x86_64 CPUs without AVX2 run ChaCha20 above 128 bytes on aws-lc's
`chacha-x86_64` SSSE3 routine, four blocks at a time, as aws-lc picks it,
which measured 2.4-2.7x faster than HACL*'s rounds from 256 bytes on Coffee
Lake, Zen 3, and Arrow Lake. Up to that, and at every length without SSSE3,
where aws-lc runs its integer routine, they run HACL*'s verified rounds, which
took 0.92-1.07 of that routine's time on the same CPUs. Header protection without AVX2 takes 0.91 of
aws-lc-rs's time on an EPYC 9V74 and 0.96 on a Xeon Platinum 8573C in
[run 41697909102].

QUIC header protection runs HACL*'s verified rounds in general-purpose
registers on every architecture, one block straight from the key and sample,
and `proofs/` proves it end to end against RFC 9001 and RFC 8439, the rounds
included. On a Neoverse-N2 it took 0.87 of the time of the code it replaced,
Graviola's NEON block, on aarch64, and 0.79 of aws-lc's `chacha-armv4` on
armv7, in [run 41861521276] against [run 41861526675].

HChaCha20, for XChaCha20, runs HACL*'s verified rounds in general-purpose
registers, as aws-lc does, except on 32-bit portable. There the unrolled
body is about 5 KiB, so ten calls to one double-round replace it. armv7
keeps the unrolled rounds. One block in vector registers is a single serial
chain, which Zen 5's two-cycle vector latency doubles. On an EPYC 9V45,
sealing 32 B with XChaCha20-Poly1305 natively takes 0.99 of aws-lc-rs's time
in [run 41585945720], against 1.11 with SSSE3 rounds in [run 41550703300].

ChaCha20-Poly1305, and XChaCha20-Poly1305 after HChaCha20, run aws-lc's
`chacha20_poly1305` assembly, which interleaves ChaCha20 with Poly1305 in one
pass: on x86_64, its AVX2 half where the CPU has AVX2 and BMI2 and its SSE4.1
half otherwise, as aws-lc picks them, and on aarch64 without SVE2, its NEON
routine. aws-lc's x86_64 routine reads its pick from `OPENSSL_ia32cap_P`;
rind's copy reads the same bits from the block rind passes it, so the path
is decided once per process like rind's others. Without SSE4.1, ChaCha20 and
Poly1305 run in separate passes, as in aws-lc. aarch64 CPUs with SVE2 run
[verified-garbage]'s one-pass routines instead, which rotate with SVE2's
`xar`: on a Neoverse N2 they took 0.60 to 0.92 of aws-lc's time at every
size. Its NEON routines took up to 1.06 of aws-lc's time at 32 to 512 bytes
on Apple's M4, though 0.65 to 0.82 opening 256 bytes and up, so CPUs
without SVE2 keep aws-lc's.

Elsewhere, 32-bit `arm` runs ChaCha20 on HACL*'s rounds and Poly1305 on
rind's 32-bit words, the radix of OpenSSL's `poly1305-armv4` integer path:
sixteen `umlal` and four small multiplies a block, against twenty-five for
26-bit limbs. 32-bit Arm NEON intrinsics are unstable on the toolchain this
crate builds with, so this backend does not ship a NEON keystream or a NEON
Poly1305. The state wipes itself on drop.
aws-lc's `chacha-armv4` and NEON Poly1305 beat that from 1200 bytes up (1.26 times
the whole seal's time at 1200 B and 1.44 times at 16 KB, on a Cortex-A7), and the
Rust is faster at 32 and 64 bytes (0.72 and 0.75 times).

[Graviola]: https://github.com/ctz/graviola
[cifra]: https://github.com/ctz/cifra
[Argon2's reference]: https://github.com/P-H-C/phc-winner-argon2
[s2n-bignum]: https://github.com/awslabs/s2n-bignum
[half-size]: https://tches.iacr.org/index.php/TCHES/article/view/12225
[HACL\*]: https://github.com/hacl-star/hacl-star
[libcrux]: https://github.com/cryspen/libcrux
[mlkem-native]: https://github.com/pq-code-package/mlkem-native
[mldsa-native]: https://github.com/pq-code-package/mldsa-native
[aws-lc]: https://github.com/aws/aws-lc
[verified-garbage]: https://github.com/pyca/verified-garbage
[fiat-crypto]: https://github.com/mit-plv/fiat-crypto
[BoringSSL]: https://boringssl.googlesource.com/boringssl
[OpenSSL]: https://github.com/openssl/openssl
[SPHINCS+]: https://github.com/sphincs/sphincsplus/tree/bas/fips205
[SUPERCOP]: https://bench.cr.yp.to/supercop.html
[curve25519-dalek]: https://github.com/dalek-cryptography/curve25519-dalek
[Wycheproof]: https://github.com/C2SP/wycheproof
[run 41550703300]: https://github.com/kixel-ai/rind/actions/runs/41550703300
[run 43881997679]: https://github.com/kixel-ai/rind/actions/runs/43881997679
[run 43531095881]: https://github.com/kixel-ai/rind/actions/runs/43531095881
[run 44169300257]: https://github.com/kixel-ai/rind/actions/runs/44169300257
[run 44171095372]: https://github.com/kixel-ai/rind/actions/runs/44171095372
[run 43881997679]: https://github.com/kixel-ai/rind/actions/runs/43881997679
[run 41585945720]: https://github.com/kixel-ai/rind/actions/runs/41585945720
[run 41657617706]: https://github.com/kixel-ai/rind/actions/runs/41657617706
[run 44171828157]: https://github.com/kixel-ai/rind/actions/runs/44171828157
[run 41678532920]: https://github.com/kixel-ai/rind/actions/runs/41678532920
[run 41697909102]: https://github.com/kixel-ai/rind/actions/runs/41697909102
[run 41861521276]: https://github.com/kixel-ai/rind/actions/runs/41861521276
[run 41861526675]: https://github.com/kixel-ai/rind/actions/runs/41861526675
[#224]: https://github.com/kixel-ai/rind/pull/224
[#281]: https://github.com/kixel-ai/rind/pull/281
[LICENSE]: LICENSE
