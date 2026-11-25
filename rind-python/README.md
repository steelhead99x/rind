# pyrind

Cryptography for Python from [rind](https://github.com/kixel-ai/rind), a
pure-Rust library: AEADs, hashes, HMAC, HKDF, PBKDF2, X25519, Ed25519, ECDSA
and ECDH, RSA, and ML-KEM, with rind's own misuse-resistant API.
[pyrind-cryptography](cryptography) offers pyca/cryptography's API on it
instead.

```shell
pip install pyrind
```

## Why

A Python call into pyca/cryptography pays OpenSSL 3's per-call setup, which
dwarfs the work on a small message. pyrind's calls go straight to rind's
assembly.

On an Intel Core i7-8700 (Coffee Lake, 2017), Linux 6.18, CPython 3.14.8,
against cryptography 50.0.2 on OpenSSL 3.5.9, one call at a time with its
inputs in hand, fastest of seven runs:

| Operation | pyrind | cryptography | hashlib, hmac | cryptography ÷ pyrind |
|---|---:|---:|---:|---:|
| SHA-256, 21 B | 262 ns | 1.79 µs | 526 ns | 6.8x |
| HMAC-SHA256, 21 B | 401 ns | 2.54 µs | 1.87 µs | 6.3x |
| HKDF-SHA256, 32 B key | 1.68 µs | 5.07 µs | - | 3.0x |
| AES-128-GCM seal, 32 B | 237 ns | 667 ns | - | 2.8x |
| AES-128-GCM open, 32 B | 218 ns | 690 ns | - | 3.2x |
| AES-128-GCM seal, 1350 B | 507 ns | 924 ns | - | 1.8x |
| AES-128-GCM open, 1350 B | 472 ns | 926 ns | - | 2.0x |
| AES-128-GCM seal, 16384 B | 3.04 µs | 3.63 µs | - | 1.2x |
| AES-128-GCM open, 16384 B | 3.02 µs | 3.59 µs | - | 1.2x |
| ChaCha20-Poly1305 seal, 32 B | 315 ns | 858 ns | - | 2.7x |
| ChaCha20-Poly1305 open, 32 B | 293 ns | 894 ns | - | 3.0x |
| ChaCha20-Poly1305 seal, 1350 B | 930 ns | 1.54 µs | - | 1.7x |
| ChaCha20-Poly1305 open, 1350 B | 901 ns | 1.59 µs | - | 1.8x |
| ChaCha20-Poly1305 seal, 16384 B | 7.13 µs | 7.66 µs | - | 1.1x |
| ChaCha20-Poly1305 open, 16384 B | 7.03 µs | 7.72 µs | - | 1.1x |
| X25519 agree | 19.93 µs | 30.44 µs | - | 1.5x |
| ECDH P-256 agree | 37.44 µs | 62.57 µs | - | 1.7x |
| Ed25519 sign, 21 B | 7.10 µs | 28.96 µs | - | 4.1x |
| Ed25519 verify, 21 B | 29.07 µs | 93.03 µs | - | 3.2x |
| ECDSA P-256 sign, 21 B | 14.41 µs | 26.14 µs | - | 1.8x |
| ECDSA P-256 verify, 21 B | 39.42 µs | 60.53 µs | - | 1.5x |
| RSA-2048 PKCS#1 sign, 21 B | 470.21 µs | 483.67 µs | - | 1.0x |
| RSA-2048 PKCS#1 verify, 21 B | 11.00 µs | 20.14 µs | - | 1.8x |
| ML-KEM-768 encapsulate | 3.22 µs | 22.16 µs | - | 6.9x |
| ML-KEM-768 decapsulate | 7.78 µs | 33.81 µs | - | 4.3x |

The gap is widest on small messages and short-lived keys, which is where
protocols spend their calls. On 16 KiB the assembly dominates both and the
two converge; RSA signing is the same modular exponentiation in each.

Run `sh/python.sh bench` in the repository for your own machine's numbers.

## Use

Each rind module is a submodule. Algorithms are constants, and a key is
made for one algorithm, so the wrong combination fails before any data
moves: passing a hash where a key wants an AEAD algorithm raises `TypeError`.

```python
import os
from pyrind import aead, digest, ecdsa, hkdf, hmac, rsa

# Hashes and MACs.
digest.digest(digest.SHA256, b"hello")
key = hmac.Key(hmac.HMAC_SHA256, b"secret")
tag = hmac.sign(key, b"message")
hmac.verify(key, b"message", tag)  # raises pyrind.BadSignature on a mismatch

# AEAD with the caller's nonces, which must never repeat under one key. The
# associated data is keyword-only, so it can't be swapped with the plaintext.
key = aead.Key(aead.AES_256_GCM, os.urandom(32))
sealed = key.seal(bytes(12), b"plaintext", aad=b"header")
assert key.open(bytes(12), sealed, aad=b"header") == b"plaintext"

# Or random 192-bit nonces, with no nonce state.
key = aead.RandomizedNonceKey(os.urandom(32))
nonce, sealed = key.seal(b"plaintext", aad=b"")
assert key.open(nonce, sealed, aad=b"") == b"plaintext"

# HKDF expands straight into keys, whose bytes never reach Python.
prk = hkdf.Salt(hkdf.HKDF_SHA256, b"salt").extract(b"input key material")
aead_key = prk.expand(b"aead", aead.AES_256_GCM)

# Signatures: each algorithm is a module with a `KeyPair` and a `PublicKey`.
# A key pair signs with a `sign` algorithm, and a peer's public key is parsed
# for a `verify` algorithm.
key_pair = ecdsa.KeyPair.generate(ecdsa.sign.P256_SHA256_ASN1)
signed = key_pair.sign(b"message")
public_key = ecdsa.PublicKey(ecdsa.verify.P256_SHA256_ASN1, bytes(key_pair.public_key()))
public_key.verify(b"message", signed)

# An RSA public key is bound to no algorithm: `verify` takes one, and refuses
# a modulus below its floor.
rsa_key_pair = rsa.KeyPair.generate(rsa.KeySize.RSA_2048)
signed = rsa_key_pair.sign(rsa.sign.PSS_SHA256, b"message")
rsa.PublicKey.from_spki(rsa_key_pair.public_key().to_spki()).verify(rsa.verify.PSS_SHA256, b"message", signed)
```

The modules are `aead`, `agreement` (X25519 and ECDH), `cipher`
(unauthenticated AES-CBC), `cpu`, `digest`, `ecdsa`, `ed25519`, `hkdf`,
`hmac`, `kem` (ML-KEM-768), `key_wrap` (AES-KW and AES-KWP, each call naming
its `Mode`), `pbkdf2`, and `rsa` (RSA signatures and RSA-OAEP). They follow
rind's own modules, so [rind's MIGRATING.md](https://github.com/kixel-ai/rind/blob/main/MIGRATING.md) maps aws-lc-rs
names to both, and [CHANGELOG.md](https://github.com/kixel-ai/rind/blob/main/rind-python/CHANGELOG.md) maps pyrind 0.1's names to
0.2's. Algorithms only legacy protocols
should use, such as SHA-1 and MD5, live in each module's `legacy` submodule.
Keys load from and encode to PKCS#8, SEC1, PKCS#1, and
`SubjectPublicKeyInfo` DER. The package ships type stubs, and
[rind's documentation](https://docs.rs/rind/) describes each operation in
depth.

Every failure raises a subclass of `pyrind.Error`: `WrongLength`,
`KeyRejected` (whose message says why), `BadSignature`, `DecryptFailed`,
`RngFailed`, `Unsupported`, or `Fault`. Arguments take any bytes-like object;
anything but `bytes` is copied first, so no other thread can change it
mid-call. RSA key generation, RSA signing and decryption, and PBKDF2 release
the GIL while they run.

pyrind wipes keys and keyed state when Python frees them, as rind does.
Nothing wipes the `bytes` a key was loaded from or exported to;
Python owns those. A key, seed, or password passed as another buffer, such
as a `bytearray` you wipe yourself, is copied for the call, and pyrind wipes
that copy before the call returns.

## Platforms

Wheels cover CPython 3.11 and later through the stable ABI, on Linux (glibc
2.17 and later on x86_64, aarch64, and armv7; musl on x86_64 and aarch64),
macOS on x86_64 and Apple silicon, and Windows on x86_64 and aarch64. PyPy,
free-threaded CPython, and other platforms build the sdist, which needs a
Rust toolchain. rind runs only on x86_64, aarch64, and 32-bit arm, so other
architectures fail to build; there is no pure-Python fallback.

## License

pyrind carries rind's licenses: rind's own code is Apache-2.0, ISC, or
MIT-0, at your option, and the code it copies keeps its source's license, as
[LICENSE](LICENSE) lists.
