# Architecture

rind's API is its own, shaped so that misuse fails to compile rather than at
run time. [MIGRATING.md][migrating] maps each ring and aws-lc-rs item to it.

- Each module takes an algorithm as a `&'static` constant, such as
  `aead::AES_128_GCM` or `signature::verify::ECDSA_P256_SHA256_ASN1`, and has
  one key type per role.
- Algorithms only old protocols should use sit in `legacy` submodules, such
  as `digest::legacy::SHA1`.
- Key pairs name the DER format they load or encode (`from_pkcs8`,
  `from_sec1`, `to_spki`), and every private key returns its public half
  from `public_key()`.
- Encodings, signatures, and shared secrets are owned values of fixed
  capacity, such as `encoding::Pkcs8`, rather than caller buffers or
  allocations. Keys wipe their secrets on drop under the `wipe` feature, and
  their `Debug` shows only their algorithm.
- No call takes a random source: rind draws from the system's when it needs
  one, and `rand::fill` gives callers the same. `drbg` is the FIPS module's
  HMAC_DRBG; rind's own key generation does not call it.
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
  `A128KW` and `A256KW`, and with padding (RFC 5649), for keys of any length.
- `agreement`: X25519 and ECDH on P-256, P-384, and P-521, with keys that
  load from a scalar, PKCS#8, or SEC1, and export as a scalar or PKCS#8, and
  peer keys parsed from a point, compressed or not, or a
  `SubjectPublicKeyInfo`.
- `kem`: ML-KEM-768.
- `hpke`: RFC 9180's base mode and secret export, over DHKEM with X25519,
  P-256, P-384, and P-521, HKDF, and the AEADs: a recipient's keys, and
  sender, recipient, and export-only contexts.
- `rsa`: RSA-OAEP encryption and decryption, with SHA-1 under `legacy`,
  and the key sizes and public-key components the RSA modules take.
- `blind_rsa`: RFC 9474's four RSABSSA-SHA384 variants: a server's key pair
  that signs blinded messages, and a public key that blinds a message,
  finalizes the reply into a signature, and verifies it, as Privacy Pass's
  publicly verifiable tokens (RFC 9578) need.
- `signature`: ECDSA on P-256, P-384, and P-521, RSA PKCS#1 v1.5 and PSS, and
  Ed25519 key pairs and verification, plus ECDSA over a `digest` the caller
  computed, with any SHA-2 hash, RSA keys given as their components, and
  SHA-1 and 1024-bit RSA for verifying old signatures. Keys load from and
  export as PKCS#8, a `SubjectPublicKeyInfo`, raw bytes, and SEC1 for ECDSA.
  ML-DSA-44, ML-DSA-65, and ML-DSA-87 (pure, with the empty context) verify
  through the same `PublicKey`, and sign with `sign::MlDsaKeyPair<P>`, whose
  parameter set is a type, so its signature is a fixed-size array.
- `digest`: MD5 and SHA-1 (legacy only), SHA-256, SHA-384, SHA-512,
  SHA-512/256, SHA3-256, SHA3-384, and SHA3-512.
- `hmac`: HMAC over SHA-1 and SHA-2, keyed once and reused.
- `hkdf`: HKDF over those HMACs, whose output becomes an `aead`, QUIC header-protection, or `hmac` key.
- `pbkdf2`: PBKDF2 over those HMACs, deriving or verifying a key from a password.
- `encoding`: the PKCS#8, SEC1, and `SubjectPublicKeyInfo` encodings key
  types export.
- `constant_time`: comparing secrets such as MACs without a timing leak.
- `rand`: random bytes from the system.
- `drbg`: SP 800-90A HMAC_DRBG over SHA-512, for the FIPS module. rind's own
  operations do not draw from it.
- `cpu`: the startup check for required CPU features, whether AES runs
  in hardware, and `Dit`, which holds data-independent timing on across a
  batch of calls.

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
architectures (`arm` only from ARMv7 on), and `portable` everywhere else, or wherever `--cfg
rind_portable` forces it. Code outside `low` gates on `rind_backend`, never
`target_arch`. `low::portable` is pure Rust and needs no CPU features; the
`arm` backend wraps its types with the crypto extension's, NEON's, and
aws-lc's assembly.

[migrating]: MIGRATING.md
