# Architecture

rind's API is its own, shaped so that misuse fails to compile rather than at
run time. [MIGRATING.md][migrating] maps each ring and aws-lc-rs item to it.

- Each module takes an algorithm as a `&'static` constant, such as
  `aead::AES_128_GCM` or `ecdsa::verify::P256_SHA256_ASN1`, and has one key
  type per role. KEMs and signing key pairs instead take a type per
  parameter set, such as `kem::DecapsulationKey<MlKem768>`, so a ciphertext or
  key of one set fails to compile against another's.
- Each signature algorithm is a module of its own, `ecdsa`, `ed25519`,
  `ml_dsa`, `rsa`, and `slh_dsa`, with a `KeyPair`, a `PublicKey`, and a
  `Signature`, so a key of one algorithm cannot reach another's call, and a
  program links only the algorithms it names. A caller that picks the
  algorithm at run time, such as a TLS stack, holds an enum of the modules'
  public keys.
- Algorithms only old protocols should use sit in `legacy` submodules, such
  as `digest::legacy::SHA1`.
- Key pairs name the DER format they load or encode (`from_pkcs8`,
  `from_sec1`, `to_pkcs8`), and every private key lends its public half
  from `public_key()`, which encodes itself (`to_spki`).
- Encodings, signatures, and shared secrets are owned values of fixed
  capacity, such as `encoding::Pkcs8`, rather than caller buffers or
  allocations. Keys wipe their secrets on drop under the `wipe` feature, and
  their `Debug` shows only their algorithm.
- No call takes a random source: rind draws from the system's when it needs
  one, and `rand::fill` gives callers the same.
- Fallible calls return `rind::Error`, whose variant says which kind of call
  failed, such as `KeyRejected` or `BadSignature`.

The modules:

- `aead`: AES-GCM and ChaCha20-Poly1305 keys with caller nonces, AES-GCM
  keys with IVs of any length and truncated tags, as WebCrypto takes, an
  XChaCha20-Poly1305 key that picks random nonces, and QUIC header-protection
  keys.
- `cipher`: bare AES, AES-CTR, and ChaCha20, for DTLS record number
  protection and SRTP.
- `key_wrap`: AES key wrap (RFC 3394), for WebCrypto's AES-KW and JWE's
  `A128KW` and `A256KW`, and with padding (RFC 5649), for keys of any length:
  one KEK serves both, and each call names its mode.
- `agreement`: X25519 and ECDH on P-256, P-384, and P-521, with keys that
  load from a scalar, PKCS#8, or SEC1, and export as a scalar or PKCS#8, and
  peer keys parsed from a point, compressed or not, or a
  `SubjectPublicKeyInfo`.
- `kem`: ML-KEM-512, ML-KEM-768, and ML-KEM-1024.
- `hpke`: RFC 9180's base mode and secret export, over DHKEM with X25519,
  P-256, P-384, and P-521, HKDF, and the AEADs: a recipient's keys, and
  sender, recipient, and export-only contexts.
- `rsa`: RSA PKCS#1 v1.5 and PSS signatures, with SHA-1 and 1024-bit keys
  under `verify::legacy` for old signatures, and RSA-OAEP encryption and
  decryption, with SHA-1 under `legacy`. A public key, from PKCS#1, a
  `SubjectPublicKeyInfo`, or its components, takes the verification
  algorithm as it verifies, which refuses a modulus below the algorithm's
  floor.
- `blind_rsa`: RFC 9474's four RSABSSA-SHA384 variants: a server's key pair
  that signs blinded messages, and a public key that blinds a message,
  finalizes the reply into a signature, and verifies it, as Privacy Pass's
  publicly verifiable tokens (RFC 9578) need.
- `oprf`: RFC 9497's OPRF over ristretto255, P-256, P-384, and P-521: a
  server's key that evaluates blinded elements, and a client's blind that
  finalizes the reply into the output. Its `voprf` mode adds the server's
  public key and a DLEQ proof over a batch, as Privacy Pass's privately
  verifiable tokens (RFC 9578) need; OPAQUE uses the base mode.
- `ecdsa`: ECDSA on P-256, P-384, and P-521, with a signature DER-encoded
  or fixed-width, plus signing and verifying a `digest` the caller computed,
  with any SHA-2 hash. Key pairs load from and export as PKCS#8, SEC1, and a
  scalar.
- `ed25519`: Ed25519 key pairs, from a seed or PKCS#8, and public keys,
  which refuse a point of small order.
- `ml_dsa`: ML-DSA-44, ML-DSA-65, and ML-DSA-87 (pure, with the empty
  context), whose parameter set is a type, so a key of one set fails to
  compile where another's is expected and a signature is a fixed-size
  array.
- `slh_dsa`: SLH-DSA's twelve parameter sets (FIPS 205, pure, with the empty
  context), whose parameter set is a type, as in `ml_dsa`. A signature, up
  to 49,856 bytes, lives on the heap.
- `frost`: RFC 9591's FROST threshold signatures over Ed25519, ristretto255,
  and P-256: a trusted dealer's shares and commitment, each signer's
  single-use nonces and signature share, and a coordinator's signing package
  that aggregates the shares and verifies each, under a group public key.
- `digest`: MD5 and SHA-1 (legacy only), SHA-256, SHA-384, SHA-512,
  SHA-512/256, SHA3-256, SHA3-384, and SHA3-512.
- `hmac`: HMAC over SHA-1 and SHA-2, keyed once and reused.
- `hkdf`: HKDF over those HMACs, whose output becomes an `aead`, QUIC header-protection, or `hmac` key.
- `pbkdf2`: PBKDF2 over those HMACs, deriving or verifying a key from a password.
- `argon2`: Argon2id, deriving or verifying a key from a password at a memory and time cost.
- `spake2plus`: SPAKE2+ on P-256 (RFC 9383, and Matter PASE's draft-01
  schedule), a password-authenticated key exchange whose suite is a type.
- `encoding`: the PKCS#8, SEC1, and `SubjectPublicKeyInfo` encodings key
  types export.
- `constant_time`: comparing secrets such as MACs without a timing leak.
- `rand`: random bytes from the system.
- `cpu`: whether AES runs in hardware, and `Dit`, which holds
  data-independent timing on across a batch of calls.

The public modules wrap three private layers:

- `low`: low level primitives. platform-specific. unsafe allowed. minimal std and alloc.
- `mid`: constructions, protocols and encodings. platform agnostic. no unsafe. minimal std and alloc.
- `high`: high level encodings and operations. platform agnostic. no unsafe.

`low` code should not refer to `mid`, nor `mid` to `high`.

`low` must present the same interface irrespective of platform.  To this end,
`low::generic` contains pure-rust polyfills for items we don't have assembler-
or intrinsic-based implementations for a certain platform.

`rind/build.rs` picks one backend per target and sets `rind_backend` to it:
`x86_64`, `aarch64`, or `arm` on little-endian targets of those
architectures (`aarch64` only with NEON, `arm` only from ARMv7 on), and `portable` everywhere else, or wherever `--cfg
rind_portable` forces it. Code outside `low` gates on `rind_backend`, never
`target_arch`. `low::portable` is pure Rust and needs no CPU features; the
`arm` backend wraps its types with the crypto extension's, NEON's, and
aws-lc's assembly.

[migrating]: MIGRATING.md
