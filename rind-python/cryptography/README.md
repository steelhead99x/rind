# pyrind-cryptography

[pyca/cryptography](https://cryptography.io)'s `hazmat` API on
[pyrind](https://github.com/moq-dev/rind/tree/main/rind-python), for what
[rind](https://github.com/moq-dev/rind), a pure-Rust library, covers. Code
switches by changing an import, and runs on rind's assembly.

Its Python layer costs part of pyrind's lead over pyca on small messages.
On an Intel Core Ultra 7 270K Plus, Linux 7.0, CPython 3.14.8, against
cryptography 50.0.2 on OpenSSL 3.5.9, one call at a time with its inputs in
hand, fastest of five runs:

| Operation | pyrind-cryptography | cryptography | cryptography ÷ pyrind-cryptography |
|---|---:|---:|---:|
| SHA-256 `Hash`, 21 B | 0.47 µs | 0.69 µs | 1.5x |
| HMAC-SHA256, 21 B | 0.63 µs | 0.90 µs | 1.4x |
| AESGCM encrypt, 32 B | 0.27 µs | 0.26 µs | 1.0x |
| X25519 exchange | 14.3 µs | 20.6 µs | 1.4x |
| ECDH P-256 exchange | 25.8 µs | 36.3 µs | 1.4x |
| Ed25519 sign, 21 B | 4.3 µs | 13.9 µs | 3.3x |
| ECDSA P-256 sign, 21 B | 7.2 µs | 15.4 µs | 2.1x |
| ECDSA P-256 verify, 21 B | 31.9 µs | 47.0 µs | 1.5x |
| RSA-2048 PKCS#1 sign, 21 B | 352 µs | 424 µs | 1.2x |

## Use

```shell
pip install pyrind-cryptography
```

Import `pyrind_cryptography` where code imports `cryptography`:

```python
from pyrind_cryptography.exceptions import InvalidSignature
from pyrind_cryptography.hazmat.primitives import hashes, serialization
from pyrind_cryptography.hazmat.primitives.asymmetric import ec

key = ec.generate_private_key(ec.SECP256R1())
signature = key.sign(b"message", ec.ECDSA(hashes.SHA256()))
key.public_key().verify(signature, b"message", ec.ECDSA(hashes.SHA256()))

pem = key.private_bytes(
    serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()
)
assert serialization.load_pem_private_key(pem, password=None).private_numbers() == key.private_numbers()
```

For a library that imports `cryptography` itself, such as pyjwt, change
its imports the same way; sh/python.sh in the repository does exactly this
to run pyjwt's and joserfc's test suites.

## Coverage

| Module | What works |
|---|---|
| `hashes` | SHA-1, SHA-256, SHA-384, SHA-512, SHA-512/256, SHA3-256, SHA3-384, SHA3-512, MD5 |
| `hmac` | over SHA-1, SHA-256, SHA-384, SHA-512 |
| `kdf` | HKDF, HKDFExpand, PBKDF2HMAC, ConcatKDFHash, ConcatKDFHMAC, X963KDF |
| `ciphers.aead` | AESGCM with 12-byte nonces, ChaCha20Poly1305 |
| `ciphers` | `Cipher` with AES in CBC and GCM modes (12-byte IVs, 16-byte tags) |
| `padding`, `keywrap` | PKCS7, ANSIX923; AES key wrap with and without padding |
| `asymmetric.ec` | ECDSA and ECDH on P-256, P-384, P-521 |
| `asymmetric.rsa` | 2048 to 8192 bits, e = 65537: PKCS#1 v1.5 and PSS signatures, OAEP |
| `asymmetric.ed25519`, `asymmetric.x25519` | all of it |
| `serialization` | PEM and DER: PKCS#8, SubjectPublicKeyInfo, PKCS#1, SEC1; OpenSSH public keys |

Everything else raises pyca's `UnsupportedAlgorithm`, never falling back to
pyca: Ed448, X448, DSA, DH, other curves (secp256k1, P-192, P-224,
Brainpool), other ciphers and modes (CTR, ECB, CFB, OFB, XTS, ChaCha20
alone), AES-CCM, -SIV, -OCB3, and -GCM-SIV, SHA-224 and BLAKE2, X.509,
encrypted private keys, OpenSSH private keys, and PKCS#12.

Within what works, it differs from pyca in these ways:

- ECDSA signs on each curve only with that curve's hash (P-256 with SHA-256,
  and so on), and its signatures are randomized, never RFC 6979's
  deterministic ones. It verifies SHA-256, SHA-384, and SHA-512 on each of
  the three curves.
- RSA signs with SHA-256, SHA-384, or SHA-512, and PSS with a salt as long as
  the digest; it verifies PKCS#1 v1.5 with SHA-1 too, and PSS with any salt
  under `PSS.AUTO`. Keys of 1024 to 2047 bits load only as public keys, and
  verify only PKCS#1 v1.5 with SHA-1, SHA-256, or SHA-512. `rsa_crt_iqmp`,
  `rsa_crt_dmp1`, `rsa_crt_dmq1`, and `rsa_recover_prime_factors` raise
  `UnsupportedAlgorithm`: they compute on the private key in Python's
  variable-time integers.
- `Cipher` in GCM mode returns nothing from `update`, writes nothing from
  `update_into`, and returns the whole message from `finalize`: rind seals
  and opens whole messages, and releases no plaintext it has not
  authenticated.
- Keys load only when rind accepts them, so a key pyca loads but rind
  refuses raises `ValueError` at load rather than later.

## Tested against

Its own tests check each primitive against pyca/cryptography and
Wycheproof. pyjwt's and joserfc's own test suites run on it, skipping only
the tests that need what rind lacks, which
[compat/pyjwt.txt](compat/pyjwt.txt) and
[compat/joserfc.txt](compat/joserfc.txt) list by reason. They need, most
often: Ed448, secp256k1 (ES256K), RSA keys under 2048 bits, X.509
certificates, RSA JWKs with only `d`, and for joserfc RSA1_5 and encrypted
PEM.

## License

pyrind-cryptography is Apache-2.0, ISC, or MIT-0, at your option; pyrind
carries rind's licenses ([LICENSE](LICENSE)).
