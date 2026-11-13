# Testing

What checks each primitive rind exports, on each backend and CPU tier it runs on.
[CONTRIBUTING.md](CONTRIBUTING.md#building-and-testing) says how to run the tests,
and [ALGORITHMS.md](ALGORITHMS.md) whose code each tier runs.

A primitive is checked five ways:

- **Vectors**: published known-answer tests, from [Wycheproof] (each file's
  name below, in `thirdparty/wycheproof/testvectors_v1/`), NIST's CAVP
  (`thirdparty/cavp/`) and [ACVP](thirdparty/acvp/README.md) samples, the RFCs, [CCTV], and the [aws-lc and BoringSSL
  files](thirdparty/vectors/README.md), run by `cargo test`.
- **Fuzz target**: a `fuzz/fuzzer/` target that compares rind with aws-lc-rs
  on fuzzed input. `fuzz.yml` runs each nightly, then replays its corpus on
  every tier and fuzzes it again against the portable backend.
- **Differential test**: a `rind/tests/crosschecks.rs` test that compares rind
  with aws-lc-rs, run by `cargo test`.
- **Constant time**: a test that marks the secrets. `admin/ctgrind` runs the
  unit tests under valgrind, which fails when a branch or address depends on a
  marked byte; the mid layer marks each key it builds, so every unit test that
  builds one is checked. `admin/ct-sde` and `admin/ct-qemu` compare the traces
  of `ct_sde_...` and `ct_qemu_...` tests for two secrets, for the code
  valgrind cannot run. `admin/ct-binsec` has [BINSEC] explore the region of
  each `ct_binsec_...` test symbolically, for every value of its secrets at
  once, on x86_64, aarch64, and the portable backend, but not on armv7,
  which stays with ctgrind and `admin/ct-qemu` since BINSEC decodes none of
  its NEON table lookups or crypto extension; it denies the CPU features
  whose instructions BINSEC cannot decode, AES-NI, VAES, the SHA512
  instructions, and AVX-512 on x86_64, and the crypto extension, SHA-3, and
  DIT on aarch64, so those paths stay with the other three, and gives it
  the effect of the few others rind and glibc run, such as aarch64's `tbl`.
  Each harness fixes its public inputs, so it checks the paths those values
  take, except that ChaCha20 and ChaCha20-Poly1305 take every message
  length up to a block and a partial one; and BINSEC's lifter
  merges a branch whose two sides are empty, so it misses a secret branch of
  that shape ([arXiv 2501.04183]).
  Of the variable-time instructions, only BINSEC sees any, divisions;
  `admin/ct-vartime` scans the release builds for all of them. Where a cell
  cites s2n-bignum's `_SAFE` theorems, they prove the routines they cover
  constant time for every input, including variable-time instructions, and
  `admin/prove bytes` checks that rind runs the code they are about.
- **Zeroing**: a `rind/tests/zeroing.rs` test that drops each value owning
  the primitive's secrets under the `wipe` feature and fails on any of its
  bytes left nonzero. It runs on every tier, native runner, and Windows.
  `rind/tests/heap_scratch.rs` checks the heap blocks each private-key
  operation frees: it runs each under two keys with the same public inputs
  and fails on a freed block whose bytes differ between them, since those
  vary with the key, and fails on any nonzero block key generation frees.
  It runs wherever the zeroing tests do, RSA key generation only in the
  nightly native and portable runs.

Separately, `low::guard_pages` checks buffer bounds. It runs each kernel
that takes a caller's slice (AES-GCM, ChaCha20-Poly1305, AES-CTR, AES-CBC,
ChaCha20, the digests and their block functions, HMAC, the constant-time
compare, and `zero_bytes`) with each slice against a `PROT_NONE` page, before and after,
at every length up to 1100 bytes and, for the AEADs, 2000 to 2600 around
AES-GCM's 512-bit kernel, so an access outside it faults. Valgrind
cannot decode the fastest tiers and AddressSanitizer does not instrument
assembly, so this is the only bounds check on them. It is an ordinary unit
test on Unix, so it runs wherever the [tier table](#tiers) runs `cargo test`;
`planted_over_read_faults` shows a read one byte past either end kills a
forked child.

`admin/testing`, in `just ci`, fails when an export, fuzz target, differential
test, constant-time test, zeroing test, vector file, or CCTV/imported-vector test is missing
from the [primitives table](#primitives), or when the table names one the code lacks.

## Tiers

`cargo test` runs the vectors and the differential tests together, so each
tier's row says where all of them run, which fuzz targets reach it, and which
constant-time checks. A primitive's cell on a tier is its row in the
[primitives table](#primitives) narrowed to what the tier's row runs. A
"denied" tier is the runner's CPU with `RIND_CPU_DISABLE_*` hiding features,
as `build.yml`, `ctgrind.yml`, and `sh/fuzz-replay.sh` set them; an SDE tier is
an Intel SDE CPU model, as `x86-cpu.yml` names them.

| Backend | Tier | Vectors and differential tests | Fuzz targets | Constant time |
|---|---|---|---|---|
| x86_64 | AVX-512 (Ice Lake and later, Zen 4 and 5) | SDE: Cannon Lake (RSA only), Granite Rapids, Diamond Rapids | SDE: Diamond Rapids; the runner's tier, when it has AVX-512 | `admin/ct-sde`: AES-GCM and RSA; ML-KEM's AVX-512 code reads only the public matrix |
| x86_64 | SHA512 instructions (Arrow Lake, Diamond Rapids) | SDE: Arrow Lake, Diamond Rapids | SDE: Diamond Rapids | `admin/ct-sde`: HMAC |
| x86_64 | VAES without AVX-512 (Alder Lake, Zen 3) | SDE: Alder Lake, Granite Rapids at 256 bits; the runner, when Zen 3 | SDE: Diamond Rapids, denied; the runner's tier, when Zen 3; denied, when it has AVX-512 | `admin/ct-sde`: AES-GCM |
| x86_64 | SHA extensions (Goldmont, Cannon Lake and later, Zen) | SDE: Goldmont and later | SDE: Diamond Rapids; the runner's tier | `admin/ct-sde`: HMAC |
| x86_64 | AVX2 and ADX, no SHA extensions or VAES (Broadwell to Cooper Lake) | SDE: Skylake server; denied | denied | ctgrind: valgrind hides AVX-512, VAES, and the SHA extensions, so the runner's own run lands here |
| x86_64 | AVX2 without ADX (Haswell) | SDE: Haswell; denied | denied | ctgrind: denied (`no-adx`) |
| x86_64 | AVX without AVX2 (Sandy and Ivy Bridge, Bulldozer, Jaguar) | SDE: Sandy Bridge, which runs Intel's AVX SHA; denied, which runs other vendors' | denied | ctgrind: denied (`no-avx2`); Intel's AVX SHA, which GitHub's AMD runners never pick, in the SHA `paths_match` tests |
| x86_64 | AES-NI without AVX (Westmere, Silvermont, Goldmont) | SDE: Westmere, Goldmont; denied | denied | ctgrind: denied (`no-avx`) |
| x86_64 | SSSE3 without AES-NI (Core 2, Nehalem) | SDE: Merom, Nehalem; denied | denied | ctgrind: denied (`no-aes`) |
| x86_64 | SSE2 (Pentium 4, `qemu64`) | SDE: Prescott; denied | denied | ctgrind: denied (`no-ssse3`) |
| aarch64 | crypto extension, SHA-512 and SHA-3 instructions (Graviton 3, Apple M, Cobalt 100) | `build.yml` on the arm64 runners | the arm64 runner | `admin/ct-qemu`: AES-GCM, HMAC-SHA384 and HMAC-SHA512, and ML-KEM, for SHA3's Keccak kernels; ctgrind for the rest, as the next row |
| aarch64 | crypto extension without SHA-3 (Graviton 2, Raspberry Pi 5) | denied | denied | ctgrind on the arm64 runner, which valgrind hides SHA3 from |
| aarch64 | no crypto extension (Raspberry Pi 4) | denied | denied | ctgrind: denied (`aarch64-portable`); `admin/ct-binsec`: denied |
| armv7 | crypto extension (most 32-bit Android) | `just armv7`: qemu `max` | the arm64 runner, which runs armv7 natively | `admin/ct-qemu`: AES, AES-CBC, AES-KW, AES-GCM, HMAC |
| armv7 | NEON without the crypto extension | `just armv7`: qemu Cortex-A15 | denied | ctgrind on the arm64 runner, which valgrind hides the crypto extension from |
| armv7 | no NEON | `just armv7`: qemu Cortex-A15, denied | denied | ctgrind: denied (`no-neon`) |
| portable | forced on x86_64 (`--cfg rind_portable`) | `just portable`: clippy and release vectors and differential tests | `fuzz.yml`'s `fuzz-portable` job: every target, from the x86_64 corpus and a corpus of its own | ctgrind: the `portable` job forces this backend |
| portable | 32-bit x86 (`i686`) | `just qemu i686`: clippy and release vectors and differential tests, natively on an x86_64 host; `build.yml`'s `i686-windows` and `android` jobs | the forced run's, of the same code built for x86_64 | ctgrind's forced run, of the same code built for x86_64 |
| portable | big-endian s390x | `just qemu s390x`: clippy and release vectors and differential tests under qemu | as above | ctgrind's forced run, of the same code built for x86_64 |
| portable | riscv64gc Linux, glibc and musl | `just qemu riscv64` and `just qemu riscv64-musl`: as s390x | as above | as s390x |
| portable | PowerPC Linux: powerpc64le, big-endian powerpc64 and powerpc | `just qemu powerpc64le`, `just qemu powerpc64`, and `just qemu powerpc`: as s390x | as above | as s390x |
| portable | ARM before ARMv7 (Raspberry Pi 1 and Zero) | `just qemu armv6` and `just qemu armv6-softfloat`: as s390x, on qemu's ARM1176; `build.yml`'s `android` job: ARMv5TE Android | as above | as s390x |
| portable | wasm32-wasip2 | `just wasm`: release vectors under wasmtime, in the nightly `build.yml`; no differential tests, since aws-lc does not build for wasm, and `just portable` runs the same Rust against it | as above | unchecked: a wasm engine compiles rind again, and its JIT may turn a select into a branch |

## Vector suites

`aws_lc::NAME` and `cctv::NAME` below are tests in
[`rind/tests/aws_lc.rs`](rind/tests/aws_lc.rs) and
[`rind/tests/cctv.rs`](rind/tests/cctv.rs). The former reads the files under
`thirdparty/vectors/aws-lc/` and `thirdparty/vectors/boringssl/`; the latter
reads CCTV's `ed25519/ed25519vectors.json`. The tests run only the algorithms,
key forms, and operations rind supports in these mixed upstream files.
Their EVP cases cover key loading as well as the operations listed below;
randomized signatures and encryption are checked by verification or round trips.

The unit tests named below read the remaining imported sets: ECDSA signing
and verification with fixed digests/nonces, BoringSSL's ML-KEM-768 (including
NIST's vectors), Miller-Rabin, modular multiplication and exponentiation,
P-256 point addition, and Poly1305. P-256's point-addition test runs only on
x86_64, for affine inputs supported by rind's routine. The modular ones run
each unproven Montgomery and RSAZ routine of the backend that takes the
modulus's width, not only the one the CPU picks; beside them, each routine's
unit tests compare it with proven or portable arithmetic on values built from
edge-case limbs, in its own radix. Poly1305's standalone test runs on x86_64, aarch64, and the 64-bit
portable backend; the AEAD vectors check the other Poly1305 implementations.

CCTV's ML-KEM tests read `ML-KEM/{intermediate,unluckysample,strcmp,modulus}/`.
The first two use draft keys to check encapsulation and decapsulation, not
final-standard key generation. The modulus cases check key rejection.
`high::kem::cctv_accumulated` derives final-FIPS-203 key-generation,
encapsulation, decapsulation, and implicit-rejection cases from a SHAKE stream,
with 10,000 cases by default and 1,000,000 with `SLOW_TESTS=1`. CCTV's RFC 6979
rejection case is embedded in `high::ecdsa::rfc6979_test_vectors`.

The `acvp_...` unit tests read NIST's ACVP sample sets in `thirdparty/acvp/`,
which `admin/sync-acvp` trims to the groups rind runs; a group a test does not
expect fails it. The SHA-2 and SHA-3 sets' 1 to 8 GiB messages run only with
`SLOW_TESTS=1`. HMAC_DRBG and ECDH read CAVP's files, as ACVP's samples test
neither as rind uses them.

These suites run wherever the [tier table](#tiers) runs `cargo test`, including
the forced portable backend. The nightly `build.yml` runs the million-case
accumulation in native release builds, on every denied x86_64/aarch64 tier,
and through `just portable`. `just armv7` and `x86-cpu.yml`'s SDE models use
the default 10,000 cases, even though they build in release mode.

## Undefined behavior

The nightly `miri` workflow, or `just miri TARGET`, runs the portable
backend's tests under [Miri] with `wipe` on, forced on x86_64 and again as
big-endian `s390x-unknown-linux-gnu`. Miri fails a test on undefined behavior,
such as a key type's wipe leaving an invalid value for the drop that follows,
a misaligned or out-of-bounds pointer, or a data race in `ReuseCache`, in rind
or in the libcrux, fiat-crypto, and curve25519-dalek code it calls; a
byte-order assumption fails the test's own assertions on s390x. Miri runs no
assembly, so the other backends are out. It runs nightly, not on pull
requests: a run takes hours, so a change to the portable backend runs
`just miri` locally or dispatches the workflow before it lands.

Miri runs each test hundreds of times slower than a native build, so it runs a
subset: the unit tests and `tests/cpu.rs` and `tests/debug.rs`, without the
tests `sh/miri.sh` lists as slow, which are the vector sets and long loops
over inputs, RSA private-key operations beyond one for each key type, and the
tests that run many scalar multiplications. A test that repeats one code path
over parameter sets or cases runs only those that take each branch under
`cfg(miri)`, as ML-DSA's do. Every primitive keeps a test that builds, uses,
and drops its keys. Miri cannot run aws-lc's C, so its builds leave out
aws-lc-rs and the differential tests, `tests/crosschecks.rs` and
`tests/cctv.rs` among them.
`tests/wycheproof.rs` and `tests/aws_lc.rs` are vector sets too, and
`tests/zeroing.rs` reads a dropped value on purpose.

## Primitives

A cell's "none" says why, or links the quest that fills it.
Verification and encryption under a public key handle no secret, so their
constant-time and zeroing cells are empty by design. A row that marks a
secret names a zeroing test, or says why it has none.

| Primitive | Exports | Vectors | Fuzz target | Differential test | Constant time | Zeroing |
|---|---|---|---|---|---|---|
| AES-GCM | `aead::{Algorithm, Key, Nonce, Tag, AES_128_GCM, AES_192_GCM, AES_256_GCM}`, `aead::gcm::{Iv, Key, Tag, TagLength}` | `aes_gcm_test`, `aes_gmac_test`, `cavp/gcm`, `aws_lc::aead`, `aws_lc::cipher`, `aws_lc::gcm`, ACVP: `aead::gcm::acvp` | `fuzz::aead`, with any IV and tag length | `crosschecks::aead::aes_gcm`, `crosschecks::aead::aes_gcm_every_length`, `crosschecks::aead::aes_gcm_any_iv` | ctgrind: `low::x86_64::aes_gcm::paths_match`, `low::x86_64::aes_gcm::counter_wraps`, `low::aarch64::aes_gcm::kernels_match_composed`, armv7 and portable keys `mid::portable::aes_gcm::new`; SDE: `low::x86_64::aes_gcm::ct_sde_aes128_gcm`, `low::x86_64::aes_gcm::ct_sde_aes192_gcm`, `low::x86_64::aes_gcm::ct_sde_aes256_gcm`, `low::x86_64::aes_gcm::ct_sde_aes_gcm_vaes_avx2`; qemu: `mid::portable::aes_gcm::ct_qemu_aes_gcm`; BINSEC, but not on aarch64, where it cannot finish the NEON GHASH in a nightly's time: `test::binsec::ct_binsec_aes_gcm` | `zeroing::aead` |
| ChaCha20-Poly1305 | `aead::{Algorithm, Key, Nonce, Tag, CHACHA20_POLY1305}` | `chacha20_poly1305_test`, RFC 8439: `mid::chacha20poly1305::test_vector`, `aws_lc::aead`, standalone Poly1305: `low::generic::poly1305::aws_lc` | `fuzz::aead` | `crosschecks::aead::chacha20_poly1305` | ctgrind: the key `mid::chacha20poly1305::new`, `low::x86_64::chacha20poly1305::paths_match`, `low::aarch64::chacha20poly1305::matches_separate_passes`, `low::arm::chacha_armv4::neon_matches_nohw`, `low::arm::poly1305::neon_matches_portable`; BINSEC: `test::binsec::ct_binsec_chacha20_poly1305` | `zeroing::aead` |
| XChaCha20-Poly1305 | `aead::{RandomizedNonceKey, RandomNonce}` | `xchacha20_poly1305_test`, draft-irtf-cfrg-xchacha: `mid::xchacha20poly1305::test_vector`, `aws_lc::aead` | `fuzz::xchacha` | `crosschecks::aead::xchacha20_poly1305` | ctgrind: the key `mid::xchacha20poly1305::new`; BINSEC: `test::binsec::ct_binsec_xchacha20_poly1305` | `zeroing::aead` |
| QUIC header protection | `aead::quic::{Algorithm, AES_128, AES_256, CHACHA20, HeaderProtectionKey, SAMPLE_LEN}` | RFC 9001: `aead::quic::rfc9001` | `fuzz::cipher` | `crosschecks::cipher::quic_header_protection_mask` | ctgrind: AES's key, as below, and ChaCha20's `mid::chacha20::new`; qemu: `mid::aes::ct_qemu_aes`; BINSEC: `test::binsec::ct_binsec_quic_header_protection` | `zeroing::aead` |
| AES block | `cipher::{Aes, Algorithm, AES_128, AES_192, AES_256}` | `cavp/aes`, `aws_lc::aes`, `aws_lc::cipher`, ACVP: `mid::aes::acvp_ecb` | `fuzz::cipher` | `crosschecks::cipher::aes_block` | ctgrind: `mid::aes::expand_key`, `mid::aes::encrypt_block`; qemu: `mid::aes::ct_qemu_aes`; BINSEC: `test::binsec::ct_binsec_aes` | `zeroing::cipher` |
| AES-CTR | `cipher::AesCtr` | SP 800-38A: `mid::aes::sp800_38a`, RFC 3686: `mid::aes::rfc3686`, RFC 3711: `mid::aes::srtp_aes_cm`, `aws_lc::cipher`, ACVP: `mid::aes::acvp_ctr` | `fuzz::cipher` | `crosschecks::cipher::aes_ctr` | ctgrind: `mid::aes::expand_key`, `mid::aes::apply_keystream`; qemu: `mid::aes::ct_qemu_aes`; BINSEC: `test::binsec::ct_binsec_aes` | `zeroing::cipher` |
| AES-CBC | `cipher::{AesCbcDecryptingKey, AesCbcEncryptingKey, CbcIv}` | `aes_cbc_pkcs5_test`, SP 800-38A: `mid::aes_cbc::sp800_38a`, `aws_lc::cipher`, ACVP: `mid::aes_cbc::acvp` | `fuzz::aes_cbc` | `crosschecks::cipher::aes_cbc_pkcs7`, `crosschecks::cipher::aes_cbc_unpadded` | ctgrind: the key `mid::aes_cbc::new`; qemu: `mid::aes_cbc::ct_qemu_aes_cbc`; BINSEC: `test::binsec::ct_binsec_aes_cbc` | `zeroing::cipher` |
| ChaCha20 | `cipher::ChaCha20` | `chacha20_counter_test`, RFC 8439: `mid::chacha20::rfc8439` | `fuzz::cipher` | `crosschecks::cipher::chacha20_keystream`, `crosschecks::cipher::chacha20_every_length` | ctgrind: the key `mid::chacha20::new`, `low::x86_64::chacha20::paths_match`, `low::arm::chacha_armv4::neon_matches_nohw`; BINSEC: `test::binsec::ct_binsec_chacha20` | `zeroing::cipher` |
| AES-KW, AES-KWP | `key_wrap::{AesKek, AES_128, AES_192, AES_256}` | `aes_wrap_test`, `aes_kwp_test`, RFC 3394: `mid::aes_kw::rfc3394`, RFC 5649: `mid::aes_kw::rfc5649`, `aws_lc::aes`, ACVP: `mid::aes_kw::acvp_kw`, `mid::aes_kw::acvp_kwp` | `fuzz::key_wrap` | `crosschecks::key_wrap::wrap_and_unwrap`, `crosschecks::key_wrap::wrap_and_unwrap_padded` | ctgrind: the key `mid::aes_kw::new`; qemu: `mid::aes_kw::ct_qemu_aes_kw`; BINSEC: `test::binsec::ct_binsec_aes_kw` | `zeroing::key_wrap` |
| MD5 | `digest::legacy::MD5` | RFC 1321: `mid::md5::rfc1321` | `fuzz::legacy` | `crosschecks::hashes_match_aws_lc_rs`, `crosschecks::hashes_every_length` | ctgrind: `high::digest::secret_message`; BINSEC: `test::binsec::ct_binsec_digest` | none: a digest context is not wiped |
| SHA-1 | `digest::legacy::SHA1` | `cavp-sha1` | `fuzz::legacy` | `crosschecks::hashes_match_aws_lc_rs`, `crosschecks::hashes_every_length` | ctgrind: `high::digest::secret_message`, each x86_64 path `low::x86_64::sha1::paths_match_generic`; SDE and qemu: through HMAC; BINSEC: `test::binsec::ct_binsec_digest` | none: a digest context is not wiped |
| SHA-2 | `digest::{Algorithm, Context, Digest, digest, SHA256, SHA384, SHA512, SHA512_256}` | `cavp/sha2`, ACVP: `high::digest::acvp_sha256`, `high::digest::acvp_sha384`, `high::digest::acvp_sha512`, `high::digest::acvp_sha512_256` | `fuzz::sha2` | `crosschecks::hashes_match_aws_lc_rs`, `crosschecks::hashes_every_length` | ctgrind: `high::digest::secret_message`, each x86_64 path `low::x86_64::sha256::paths_match_generic`, `low::x86_64::sha512::paths_match_nohw`; SDE and qemu: through HMAC; BINSEC: `test::binsec::ct_binsec_digest` | none: a digest context is not wiped |
| SHA-3 | `digest::{SHA3_256, SHA3_384, SHA3_512}` | `cavp/sha3`, ACVP: `high::digest::acvp_sha3_256`, `high::digest::acvp_sha3_384`, `high::digest::acvp_sha3_512` | `fuzz::sha3` | `crosschecks::hashes_match_aws_lc_rs`, `crosschecks::hashes_every_length` | ctgrind: `high::digest::secret_message`; proof: on aarch64, s2n-bignum's _SAFE theorems, for the routines [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists with one; qemu: aarch64's SHA3 kernels through ML-KEM; BINSEC: `test::binsec::ct_binsec_digest` | none: a digest context is not wiped |
| HMAC | `hmac::{Algorithm, Context, Key, Tag, sign, verify, HMAC_SHA256, HMAC_SHA384, HMAC_SHA512}`, `hmac::legacy::HMAC_SHA1` | `hmac_sha*_test`, `cavp/hmac`, `aws_lc::hmac`, ACVP: `high::hmac::acvp` | `fuzz::legacy`, `fuzz::sha2` | `crosschecks::hmac_matches_aws_lc_rs` | ctgrind: `high::hmac::secret_key_and_message`; SDE: `high::hmac::ct_sde_hmac`; qemu: `high::hmac::ct_qemu_hmac`; BINSEC: `test::binsec::ct_binsec_hmac` | `zeroing::hmac` |
| HKDF | `hkdf::{Algorithm, KeyType, Okm, Prk, Salt, HKDF_SHA256, HKDF_SHA384, HKDF_SHA512}`, `hkdf::legacy::HKDF_SHA1` | `hkdf_sha*_test`, RFC 5869: `high::hkdf::rfc5869`, ACVP's SP 800-56C KDA: `high::hkdf::acvp_kda` | `fuzz::hkdf` | `crosschecks::hkdf::matches_aws_lc_rs`, `crosschecks::hkdf::keys` | ctgrind: `high::hkdf::secret_ikm`; BINSEC: `test::binsec::ct_binsec_hkdf` | `zeroing::hkdf` |
| PBKDF2 | `pbkdf2::{Algorithm, Secret, PBKDF2_HMAC_SHA256, PBKDF2_HMAC_SHA384, PBKDF2_HMAC_SHA512}`, `pbkdf2::legacy::PBKDF2_HMAC_SHA1` | `pbkdf2_hmacsha*_test` | `fuzz::pbkdf2` | `crosschecks::pbkdf2::matches_aws_lc_rs` | ctgrind: `high::pbkdf2::secret_password`; BINSEC: `test::binsec::ct_binsec_pbkdf2` | `zeroing::pbkdf2` |
| X25519 | `agreement::{Algorithm, PrivateKey, PublicKey, Scalar, SharedSecret, X25519}` | `x25519_test`, `x25519_asn_test`, `aws_lc::evp`, ACVP: `high::agreement::acvp_x25519`, `high::agreement::acvp_x25519_key_gen`, `high::agreement::acvp_x25519_key_ver` | `fuzz::kx`, `fuzz::keys` | `crosschecks::ecdh_scalars::x25519`, `crosschecks::ecdh_scalars::x25519_pkcs8` | ctgrind: the key `mid::x25519::from_bytes`, `mid::x25519::new_random`, `high::agreement::loads_in_constant_time`, `low::arm::curve25519::neon_matches_dalek`; proof: on x86_64, s2n-bignum's _SAFE theorems, for the routines [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists with one; BINSEC: `test::binsec::ct_binsec_x25519` | `zeroing::ecdh` |
| ECDH P-256, P-384, P-521 | `agreement::{Algorithm, PrivateKey, PublicKey, Scalar, SharedSecret, ECDH_P256, ECDH_P384, ECDH_P521}` | `ecdh_secp*r1_test`, `ecdh_secp*r1_ecpoint_test`, `cavp/ecdsa` (key pairs and public key validation), `aws_lc::ecdh`, `aws_lc::ec_scalar_base_mult`, `aws_lc::evp`; x86_64 P-256 point addition: `low::x86_64::ecp_nistz256::aws_lc_point_add_affine`, `cavp/ecdh`: `high::agreement::cavp_ecdh` | `fuzz::kx`, `fuzz::keys` | `crosschecks::ecdh`, `crosschecks::ecdh_stored`, `crosschecks::ecdh_scalars::p256` | ctgrind: the keys `mid::p256::from_bytes`, `mid::p256::generate`, `mid::p384::from_bytes`, `mid::p384::generate`, `mid::p521::from_bytes`, `mid::p521::generate`, `high::agreement::loads_in_constant_time`; proof: s2n-bignum's _SAFE theorems, but not for P-256's scalar multiplications on aarch64 or its variable-base one on x86_64, for the routines [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists with one; BINSEC: `test::binsec::ct_binsec_ecdh_p256`, `test::binsec::ct_binsec_ecdh_p384`, `test::binsec::ct_binsec_ecdh_p521` | `zeroing::ecdh` |
| ML-KEM-768 | `kem::{Algorithm, Ciphertext, DecapsulationKey, EncapsulationKey, SharedSecret, ML_KEM_768}` | `mlkem_768*_test`, `high::kem::boringssl`, `high::kem::cctv_intermediate`, `high::kem::cctv_unlucky_sample`, `high::kem::cctv_strcmp`, `high::kem::cctv_modulus`, `high::kem::cctv_accumulated`, ACVP: `mid::mlkem768::acvp_key_gen`, `mid::mlkem768::acvp_encap_decap` | `fuzz::kem`, `fuzz::keys` | `crosschecks::mlkem768::encapsulated_by_ours`, `high::kem::encapsulated_by_theirs` | ctgrind: `mid::mlkem768::keygen_internal`, `mid::mlkem768::encaps_internal`; proof: on aarch64, and on x86_64 only for reduction and rejection sampling, s2n-bignum's _SAFE theorems, for the routines [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists with one; qemu: `mid::mlkem768::ct_qemu_mlkem768`; BINSEC: `test::binsec::ct_binsec_mlkem768` | `zeroing::mlkem768` |
| HPKE | `hpke::{Aead, EncapsulatedKey, Exporter, Kdf, Kem, PrivateKey, PublicKey, Recipient, Sender, Suite, AES_128_GCM, AES_256_GCM, CHACHA20_POLY1305, DHKEM_P256_HKDF_SHA256, DHKEM_P384_HKDF_SHA384, DHKEM_P521_HKDF_SHA512, DHKEM_X25519_HKDF_SHA256, HKDF_SHA256, HKDF_SHA384, HKDF_SHA512}` | `hpke_x25519_*_test`, RFC 9180 (X25519, P-256, and P-521 KEMs): `high::hpke::rfc9180` | `fuzz::hpke`, against rustls's aws-lc-rs provider | `crosschecks::hpke::matches_hpke_rs`, against hpke-rs, as aws-lc-rs has no HPKE; rind-rustls's tests/hpke.rs compares its suites with rustls's aws-lc-rs provider's | ctgrind: `high::hpke::secret_decapsulation`, `high::hpke::secret_key_derivation`; the keys, as X25519 and ECDH above | `zeroing::hpke` |
| Ed25519 signing | `signature::{Ed25519KeyPair, Ed25519Seed}` | RFC 8032: `mid::ed25519::test_rfc8032_test_vectors`, `aws_lc::ed25519`, `aws_lc::evp`, ACVP: `high::ed25519::acvp_key_gen`, `high::ed25519::acvp_sig_gen` | `fuzz::sign`; its seeds load in `fuzz::keys` | `crosschecks::ed25519::sign_verify`, `crosschecks::ed25519::seed_alone`, `crosschecks::ed25519::seed_and_public_key`, `crosschecks::ed25519_key_generation` | ctgrind: the seed `mid::ed25519::from_seed`, armv7 and portable seeds `mid::portable::ed25519::from_seed`; proof: s2n-bignum's _SAFE theorems, for the routines [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists with one; BINSEC: `test::binsec::ct_binsec_ed25519` | `zeroing::ed25519` |
| Ed25519 verification | `signature::{PublicKey, Signature, VerificationAlgorithm}`, `signature::verify::ED25519` | `ed25519_test`, `aws_lc::ed25519`, `aws_lc::evp`, `cctv::ed25519_edge_cases` (small-order keys refused), ACVP: `high::ed25519::acvp_key_ver`, `high::ed25519::acvp_sig_ver` | `fuzz::verify`, `fuzz::keys` | `crosschecks::ed25519::small_order_public_keys` | | |
| ECVRF | `vrf::{Algorithm, Output, Proof, PublicKey, SecretKey, SecretKeyBytes, ECVRF_EDWARDS25519_SHA512_TAI, ECVRF_P256_SHA256_TAI}` | RFC 9381: `high::vrf::rfc9381_vectors`, and refused proofs and keys: `high::vrf::refuses_altered_proofs`, `high::vrf::refuses_unreduced_s`, `high::vrf::refuses_bad_public_keys` | `fuzz::vrf`, against itself, as no reference runs on aws-lc | `crosschecks::vrf::matches_akd`, against akd_core for Edwards25519, and `crosschecks::vrf::matches_vrf_rfc9381`, against vrf-rfc9381 for P-256, as aws-lc-rs has no VRF | ctgrind: secret keys are marked when loaded, `high::vrf::stays_secret` | `zeroing::vrf` |
| OPRF, VOPRF | `oprf::{Blind, BlindedElement, EvaluatedElement, Output, ServerKey, ServerKeyBytes, Suite, P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512}`, `oprf::voprf::{Blind, EvaluatedElements, Proof, PublicKey, ServerKey}` | RFC 9497: `high::oprf::tests::rfc9497_oprf_vectors`, `high::oprf::voprf::tests::rfc9497_voprf_vectors`, and refused proofs, keys, elements, batches, and lengths: `high::oprf::voprf::tests::refuses_altered_proofs`, `high::oprf::voprf::tests::refuses_bad_public_keys`, `high::oprf::voprf::tests::refuses_bad_batches`, `high::oprf::tests::refuses_bad_keys`, `high::oprf::tests::refuses_bad_elements`, `high::oprf::tests::refuses_long_inputs` | `fuzz::oprf`, against itself, as no reference runs on aws-lc | `crosschecks::oprf::ristretto255_matches_voprf`, `crosschecks::oprf::p256_matches_voprf`, `crosschecks::oprf::p384_matches_voprf`, `crosschecks::oprf::p521_matches_voprf`, against the voprf crate in both modes, as aws-lc-rs has no OPRF | ctgrind: server keys are marked when loaded, `high::oprf::tests::stays_secret`, `high::oprf::voprf::tests::stays_secret` | `zeroing::oprf` |
| ristretto255 and edwards25519 scalar multiplication | none: crate-internal, under the OPRF's ristretto255 suite | `ristretto255_scalar_invert_test`, RFC 9496: `mid::ristretto255_tests::rfc9496_multiples_of_the_generator`, `mid::ristretto255_tests::rfc9496_invalid_encodings`, `mid::ristretto255_tests::rfc9496_from_uniform_bytes`, `mid::edwards25519::sqrt_ratio_m1_vectors`, RFC 9497: `mid::ristretto255_tests::rfc9497_oprf` | through `fuzz::oprf` | `mid::ristretto255_tests::matches_dalek`, against curve25519-dalek, as aws-lc-rs has no ristretto255; armv7 and portable run dalek's, so there it checks only the wrapping | ctgrind: `mid::ristretto255_tests::constant_time`, decoding only on x86_64 and aarch64, as dalek's branches on whether an encoding is valid | `zeroing::oprf`, whose keys and blinds hold its scalars |
| ECDSA signing | `signature::{EcdsaKeyPair, EcdsaScalar, EcdsaSigningAlgorithm}`, `signature::sign::{ECDSA_P256_SHA256_ASN1, ECDSA_P256_SHA256_FIXED, ECDSA_P384_SHA384_ASN1, ECDSA_P384_SHA384_FIXED, ECDSA_P521_SHA512_ASN1, ECDSA_P521_SHA512_FIXED}` | RFC 6979 and CCTV rejection: `high::ecdsa::rfc6979_test_vectors`, `high::ecdsa::rfc6979_p521_test_vectors`; `high::ecdsa::aws_lc_sign`, `aws_lc::evp`, ACVP: `high::ecdsa::acvp_key_gen`, `high::ecdsa::acvp_sig_gen`, `high::ecdsa::acvp_det_sig_gen`; its nonces' HMAC_DRBG: `cavp/drbg`, `high::hmac_drbg::cavp` | `fuzz::sign`; its keys load in `fuzz::keys` | `crosschecks::ecdsa`, `crosschecks::ecdsa_digest::theirs_verify_ours`, `crosschecks::pkcs8_attributes::ecdsa_and_rsa_refuse_v2`, `crosschecks::pkcs8_attributes::attributes` | ctgrind: the keys, as for ECDH, and `high::signature::ecdsa_signs_and_verifies_any_digest`; proof: s2n-bignum's _SAFE theorems, but not for P-256's scalar multiplications on aarch64,, for the routines [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists with one; BINSEC: `test::binsec::ct_binsec_ecdsa_p256`, `test::binsec::ct_binsec_ecdsa_p384`, `test::binsec::ct_binsec_ecdsa_p521` | `zeroing::ecdsa` |
| ECDSA verification | `signature::{PublicKey, Signature, VerificationAlgorithm}`, `signature::verify::{ECDSA_P256_SHA256_ASN1, ECDSA_P256_SHA256_FIXED, ECDSA_P256_SHA384_ASN1, ECDSA_P256_SHA512_ASN1, ECDSA_P384_SHA256_ASN1, ECDSA_P384_SHA384_ASN1, ECDSA_P384_SHA384_FIXED, ECDSA_P384_SHA512_ASN1, ECDSA_P521_SHA256_ASN1, ECDSA_P521_SHA384_ASN1, ECDSA_P521_SHA512_ASN1, ECDSA_P521_SHA512_FIXED}` | `ecdsa_secp*_test`, `cavp/ecdsa`, `high::ecdsa::aws_lc_verify`, `aws_lc::evp`, ACVP: `high::ecdsa::acvp_key_ver`, `high::ecdsa::acvp_sig_ver` | `fuzz::verify`, `fuzz::keys` | `crosschecks::public_key_forms`, `crosschecks::ecdsa_digest::ours_verify_theirs` | | |
| RSA signing and key generation | `signature::{RsaKeyPair, RsaPssSaltLength, RsaSigningAlgorithm}`, `signature::sign::{RSA_PKCS1_SHA256, RSA_PKCS1_SHA384, RSA_PKCS1_SHA512, RSA_PSS_SHA256, RSA_PSS_SHA384, RSA_PSS_SHA512}`, `rsa::KeySize` | `rsa_pkcs1_*_sig_gen_test`, Wycheproof's primality tests: `mid::rsa_priv::generate::test_valid_primes`, `aws_lc::evp`, `mid::rsa_priv::generate::aws_lc_miller_rabin`, modular products: `low::posint::aws_lc_mod_mul`, `low::x86_64::mont::aws_lc_mod_mul`, `low::aarch64::mont::aws_lc_mod_mul`, `low::arm::mont::aws_lc_mod_mul`, exponentiation: `low::posint::aws_lc_mod_exp`, `low::x86_64::mont_exp::aws_lc_mod_exp`, `low::x86_64::rsaz::aws_lc_mod_exp`, `low::x86_64::rsaz_avx512::aws_lc_mod_exp`, ACVP: `high::rsa::acvp_sig_gen`, `mid::rsa_priv::acvp_signature_primitive` | `fuzz::sign`, which also checks that aws-lc-rs loads the key rind generates as it starts; its keys load in `fuzz::keys` | `crosschecks::rsa::sign_verify`, `crosschecks::rsa::pss_salt_lengths`, `crosschecks::rsa::key_generation_2048`, `crosschecks::rsa::key_generation_2048_soak`, `crosschecks::rsa::key_generation_3072`, `crosschecks::rsa::key_generation_4096`, `crosschecks::rsa::key_generation_6144`, `crosschecks::rsa::key_generation_8192`, `crosschecks::rsa::pkcs8_algorithms_agree` | ctgrind: private keys are marked when loaded, `mid::rsa_priv::generate::random_prime_one`; SDE: `low::x86_64::rsaz_avx512::ct_sde_rsa2048`, `low::x86_64::rsaz_avx512::ct_sde_rsa3072`, `low::x86_64::rsaz_avx512::ct_sde_rsa4096`; BINSEC of loading the key and signing, at 2048 bits, and at 3072 on x86_64, where its 24-word primes take other code; at 4096 bits, of the 32-word Montgomery products, as BINSEC cannot finish the exponentiation in a nightly's time: `test::binsec::ct_binsec_rsa2048_sign`, `test::binsec::ct_binsec_rsa3072_sign`, `test::binsec::ct_binsec_mont_mul` | `zeroing::rsa` |
| RSA verification | `signature::{PublicKey, RsaVerificationAlgorithm, Signature}`, `signature::verify::{RSA_PKCS1_SHA256, RSA_PKCS1_SHA384, RSA_PKCS1_SHA512, RSA_PSS_SHA256, RSA_PSS_SHA256_ANY_SALT, RSA_PSS_SHA384, RSA_PSS_SHA384_ANY_SALT, RSA_PSS_SHA512, RSA_PSS_SHA512_ANY_SALT}`, `signature::verify::legacy::{RSA_PKCS1_1024_SHA1, RSA_PKCS1_1024_SHA256, RSA_PKCS1_1024_SHA512, RSA_PKCS1_3072_SHA384, RSA_PKCS1_SHA1}`, `rsa::PublicKeyComponents` | `rsa_signature_*_test`, `rsa_pss_*_test`, `rsa_pkcs1_*_sig_gen_test`, `aws_lc::evp`, ACVP: `high::rsa::acvp_sig_ver` | `fuzz::verify`, `fuzz::keys` | `crosschecks::rsa::verification_agrees`, `crosschecks::rsa::refuses_modulus_below_2048_bits`, `crosschecks::rsa::refuses_exponent_over_33_bits`, `crosschecks::rsa::spki_forms_agree` | | |
| ML-DSA signing | `signature::sign::{MlDsaKeyPair, MlDsaParameterSet, MlDsaSeed, MlDsaSignature, MlDsa44, MlDsa65, MlDsa87}` | `mldsa_*_sign_seed_test`, `mldsa_*_sign_noseed_test`, ACVP: `mid::mldsa::acvp_key_gen`, `mid::mldsa::acvp_sig_gen`; the portable arithmetic against the AVX2 and Neon routines: `low::generic::mldsa_poly::backend_matches_port` | `fuzz::keys`, which signs with each key it loads | `crosschecks::ml_dsa_44::sign_verify`, `crosschecks::ml_dsa_44::expanded`, and their ML-DSA-65 and ML-DSA-87 twins | ctgrind: the seed `mid::mldsa::from_seed`, the expanded key `mid::mldsa::from_secret_key`, and the randomness `mid::mldsa::sign` draws, and every value derived from them; proof: s2n-bignum's _SAFE theorems, but not for x86_64's NTT and inverse NTT, for the routines [ALGORITHMS.md](ALGORITHMS.md#s2n-bignums-constant-time-theorems) lists with one; BINSEC, but not on aarch64, where it cannot finish in a nightly's time: `test::binsec::ct_binsec_mldsa` | `zeroing::ml_dsa` |
| ML-DSA verification | `signature::{PublicKey, VerificationAlgorithm}`, `signature::verify::{ML_DSA_44, ML_DSA_65, ML_DSA_87}` | `mldsa_*_verify_test`, ACVP: `mid::mldsa::acvp_sig_ver` | `fuzz::verify`, `fuzz::keys` | `crosschecks::ml_dsa_44::sign_verify` and its twins, both ways | | |
| RSA-OAEP | `rsa::{Ciphertext, DecryptingKey, EncryptingKey, OaepAlgorithm, Plaintext, OAEP_SHA256, OAEP_SHA384, OAEP_SHA512}`, `rsa::legacy::OAEP_SHA1` | `rsa_oaep_*_test`, `aws_lc::evp`, ACVP's decryption primitive: `mid::rsa_priv::acvp_decryption_primitive` | `fuzz::oaep` | `crosschecks::rsa::encrypt_decrypt`, `crosschecks::rsa::decrypt_agrees` | ctgrind: private keys are marked when loaded, `high::oaep::stays_secret`, `high::pkcs1::encode_oaep`; SDE: as RSA signing; BINSEC of loading the key and decrypting, at 2048 bits: `test::binsec::ct_binsec_rsa2048_oaep`, and the rest as RSA signing | `zeroing::rsa_oaep` |
| RSA blind signatures | `blind_rsa::{Algorithm, BlindSignature, BlindedMessage, Blinding, KeyPair, PublicKey, Signature, RSABSSA_SHA384_PSS_DETERMINISTIC, RSABSSA_SHA384_PSS_RANDOMIZED, RSABSSA_SHA384_PSSZERO_DETERMINISTIC, RSABSSA_SHA384_PSSZERO_RANDOMIZED}` | `rsa_pss_2048_sha384_mgf1_48_test`, `rsa_pss_4096_sha384_mgf1_48_test`, RFC 9474: `high::blind_rsa::rfc9474_vectors`, RFC 9578's token: `high::blind_rsa::rfc9578_token` | `fuzz::blind_rsa`, against itself, as no reference runs on aws-lc | `crosschecks::blind_rsa::matches_blind_rsa_signatures`, against blind-rsa-signatures, as aws-lc-rs has no blind RSA | ctgrind: private keys are marked when loaded, `high::blind_rsa::stays_secret`; SDE and BINSEC: as RSA signing | `zeroing::blind_rsa` |
| Key encodings | `encoding::{Pkcs8, Sec1, Spki}` | `aws_lc::evp` (PKCS#8, SPKI); the other keys in the files above | `fuzz::keys` | `crosschecks::encodings` | none: a key is marked once parsed, and its DER's lengths are not secret | `zeroing::ecdh`, `zeroing::ecdsa`, `zeroing::ed25519`, `zeroing::rsa` |
| Constant-time comparison | `constant_time::verify` | none: no published set | none: it returns whether two slices are equal, which the differential test covers | `crosschecks::slice_comparison_matches_aws_lc_rs` | ctgrind: `high::constant_time::contents_stay_secret`, `low::generic::ct_equal::equiv`; BINSEC: `test::binsec::ct_binsec_constant_time_verify` | none: it keeps nothing |
| Random bytes | `rand::fill` | none: the operating system's generator, which no vector can check | none, as for vectors | none, as for vectors | none: rind passes the bytes on | none: rind keeps no copy of the bytes |

Exports that are not primitives: `Error`, `KeyRejected`, `doc::inline_assembly_safety`, `cpu::Dit`, `cpu::MissingFeature`, `cpu::check`, `cpu::has_aes_hardware`.

## Adapters

Each adapter crate gets a fuzz target that feeds it a hostile peer's bytes:
records, packets, key shares, tickets, certificates, and signatures, through
the traits its upstream calls, compared with upstream's own aws-lc-rs
provider, then whole handshakes between two rind endpoints with their bytes
edited in flight. A panic, a hang, or an answer that differs from aws-lc-rs's
fails the run, as does a failed open that leaves plaintext in the caller's
buffer.

Adapter fuzz targets: `fuzz::rustls`, `fuzz::dimpl`, `fuzz::str0m`.

## Coverage

`nix develop .#coverage --command admin/coverage` measures how much of the
published code its own tests run: the `rind` crate and its adapters under
`cargo test`, rind-dart under `dart test`, and pyrind under
`sh/python.sh test`, leaving out the tools (rind-bench, rind-cpuid,
rind-timing, and the fuzzer). A function it lists as never run is published
code no test reaches. It runs the suites as the nightly jobs do, with the
vector submodules, `SLOW_TESTS=1`, and again with CPU features denied (on
x86_64, under Intel SDE too), so a plain `cargo llvm-cov` reports less. The
nightly `coverage` workflow runs it on Linux and macOS; the summary table in
its "Measure coverage" step's log is the report.

## Running the tools

On Linux, `just armv7` runs the nightly armv7 job: it builds and lints for
32-bit ARM, then runs the tests under qemu with the ARMv8 crypto extension,
with NEON alone, and with NEON denied. `just qemu <shell>` runs an entry of
the nightly `qemu` job, which lints and tests the portable backend: `s390x`
(big-endian), `riscv64`, `riscv64-musl`, `loongarch64`, `armv6` and
`armv6-softfloat` (the Raspberry Pi 1's core), or `powerpc64le`, `powerpc64`,
and `powerpc` (the last two big-endian) under qemu, or `i686` (32-bit x86)
natively.
`just miri` runs the nightly `miri` job, the portable backend's tests under
Miri, on x86_64, and `just miri s390x-unknown-linux-gnu` big-endian.
`nix develop .#ctgrind --command admin/ctgrind` runs the nightly
constant-time checks under valgrind, `nix develop .#sde --command
admin/ct-sde` those of the AVX-512, VAES, SHA extension, and SHA512 code
valgrind cannot run, under Intel SDE, and `nix develop .#ct-qemu --command
admin/ct-qemu` those of the armv7 crypto extension code valgrind hides, under
qemu; on an aarch64 host, `nix develop .#ct-qemu-aarch64 --command
admin/ct-qemu --target aarch64-unknown-linux-gnu` those of the aarch64 code
that runs only with SHA3, and `nix develop .#binsec --command admin/ct-binsec
[--exact] [test]` has BINSEC prove the region of each `ct_binsec_...` test
constant time for every secret, symbolically. None of them but BINSEC, which
sees divisions, can see an instruction whose timing depends on its
operands, so `admin/ct-vartime`, which `just check` runs when rind changes,
scans its release builds for every architecture it builds for, and its
portable backend's on x86_64 and armv7, for divisions and floating-point arithmetic, and fails on one that `admin/ct-vartime.toml` does
not list as taking only public operands.
`nix develop .#dudect --command admin/timing dudect` times each secret
operation whose secret the API lets it set (not key generation, encapsulation,
or varied ML-KEM decapsulation keys) on two classes of secret, as dudect does,
and `admin/timing marvin` runs the Marvin toolkit against RSA-OAEP decryption. They need quiet
hardware: the weekly `timing` workflow runs them on GitHub's runners, and a
shared host adds noise that no gate removes.
`nix develop .#prove --command admin/prove` checks rind's HOL Light proofs of
its assembly, then translates the Rust under proof to Lean with Aeneas and
checks the proofs in [`proofs/`](proofs/README.md).

[Wycheproof]: https://github.com/C2SP/wycheproof
[CCTV]: https://github.com/C2SP/CCTV
[Miri]: https://github.com/rust-lang/miri
[BINSEC]: https://github.com/binsec/binsec
[arXiv 2501.04183]: https://arxiv.org/abs/2501.04183
