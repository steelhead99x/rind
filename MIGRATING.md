# Migrating from ring and aws-lc-rs

This guide maps each ring 0.17 and aws-lc-rs 1.x item to rind's name, to the
[quest](quest/README.md) that adds it, or to why rind refuses it, and
surveys the crates that pick a crypto backend for you. ring's names match
aws-lc-rs's except where noted. A crate on ring that cannot change its code
renames [rind-ring](#rind-ring), ring's API on rind, to `ring`, and a binary
patches it in for every crate in its tree on ring 0.17. A crate on aws-lc-rs
renames [rind-aws-lc-rs](#rind-aws-lc-rs) to `aws-lc-rs` the same way.

## Across the API

| aws-lc-rs | rind |
|---|---|
| A `&'static` algorithm, or an `hmac::Algorithm` or `hkdf::Algorithm` by value | always `&'static` |
| A `&dyn SecureRandom` argument | none: rind draws from the system's random source itself |
| A `_FOR_LEGACY_USE_ONLY` suffix | a `legacy` submodule, such as `digest::legacy::SHA1` |
| An allocated `Document`, `Vec`, or `Box` output | an owned value of fixed capacity, such as `encoding::Pkcs8` |
| `error::Unspecified`, `error::KeyRejected` | `rind::Error`, by kind of call (see [error](#error)) |
| aws-lc-rs wipes keys and keyed state on drop; ring doesn't | rind wipes them only under its `wipe` feature: enable `rind/wipe`, or rind-aws-lc-rs's `wipe`, to keep aws-lc-rs's behavior |

## digest

| aws-lc-rs | rind |
|---|---|
| `digest(alg, data)`, `Context::{new, update}`, `Digest`'s bytes | the same |
| `Context::finish(self)` | `Context::finish(&mut self)`, which leaves the context fresh to hash another message; bind the context `mut` |
| `SHA256`, `SHA384`, `SHA512`, `SHA512_256` | the same |
| `SHA1_FOR_LEGACY_USE_ONLY` | `legacy::SHA1` |
| MD5 (in neither) | `legacy::MD5`, for hashing only: no HMAC, key derivation, or signature takes it |
| `SHA224` (not in ring) | none; [aws-lc-rs extras](quest/m3/parity/aws-lc-extras.md) |
| `SHA3_256`, `SHA3_384`, `SHA3_512` (not in ring) | the same |
| `Algorithm::output_len()` | the same |
| `Algorithm::block_len()`, `chaining_len()`, `MAX_BLOCK_LEN`, `MAX_CHAINING_LEN`, `MAX_OUTPUT_LEN`, `SHA*_OUTPUT_LEN` | none; `output_len()` gives each length |
| `Context::algorithm()`, `Digest::algorithm()` | none |
| `Digest::import_less_safe` | none: rind signs and verifies only digests it computed |

## hmac

| aws-lc-rs | rind |
|---|---|
| `Key::new(HMAC_SHA256, key)` | `Key::new(&HMAC_SHA256, key)` |
| `Key::generate(alg, rng)` | `rand::fill` a `tag_len()`-byte key, then `Key::new` |
| `Key::algorithm()` | the same, as `&'static` |
| `Context::{with_key, update, sign}`, `sign`, `Tag` | the same |
| `verify(key, data, tag)` | the same, failing with `Error::BadSignature` |
| `HMAC_SHA256`, `HMAC_SHA384`, `HMAC_SHA512` | the same |
| `HMAC_SHA1_FOR_LEGACY_USE_ONLY` | `legacy::HMAC_SHA1` |
| `HMAC_SHA224` | none; [aws-lc-rs extras](quest/m3/parity/aws-lc-extras.md) |
| `Algorithm::digest_algorithm()` | none; `Algorithm::tag_len()` gives the output length |
| `Signature`, `SigningContext`, `SigningKey`, `VerificationKey` (deprecated) | `Tag`, `Context`, `Key` |

## hkdf

| aws-lc-rs | rind |
|---|---|
| `Salt::new(HKDF_SHA256, salt)`, `extract` | `Salt::new(&HKDF_SHA256, salt)`, `extract` |
| `Salt::none(alg)` | `Salt::new(&alg, &[])`, which extracts the same key as RFC 5869's absent salt |
| `HKDF_SHA256`, `HKDF_SHA384`, `HKDF_SHA512` | the same |
| `HKDF_SHA1_FOR_LEGACY_USE_ONLY` | `legacy::HKDF_SHA1` |
| `prk.expand(info, len)?` | `prk.expand(info, len)`, which cannot fail; `Okm::fill` checks a byte length |
| your own `KeyType` | none: it is sealed, for a `usize` byte length or an `aead`, `aead::quic`, `hmac`, or `hkdf` algorithm |
| `UnboundKey::from(okm)`, `HeaderProtectionKey::from(okm)`, `hmac::Key::from(okm)`, `Prk::from(okm)` | `aead::Key::from(okm)`, `HeaderProtectionKey::from(okm)`, `hmac::Key::from(okm)`, `Prk::from(okm)` with `&HKDF_SHA256` |
| `Okm::fill(out)` | the same, for a `usize` length only |
| `Salt::from(okm)`, `Prk::new_less_safe` | none |
| `Salt::algorithm()`, `Okm::len()`, `Algorithm::hmac_algorithm()` | none |

## pbkdf2

| aws-lc-rs | rind |
|---|---|
| `derive(alg, iterations, salt, secret, out)` | `Secret::new(&alg, secret).derive(iterations, salt, out)?`, which fails with `Error::WrongLength` where aws-lc-rs panics on an overlong `out` |
| `verify(alg, iterations, salt, secret, previous)` | `Secret::new(&alg, secret).verify(iterations, salt, previous)` |
| `PBKDF2_HMAC_SHA256`, `PBKDF2_HMAC_SHA384`, `PBKDF2_HMAC_SHA512` | the same |
| `PBKDF2_HMAC_SHA1` | `legacy::PBKDF2_HMAC_SHA1` |

A `Secret` keys HMAC once, so deriving or verifying with several salts
reuses it. `verify` refuses a stored value shorter than the HMAC output with
`Error::WrongLength`, where ring and aws-lc-rs compare any prefix.

## aead

| aws-lc-rs | rind |
|---|---|
| `LessSafeKey::new(UnboundKey::new(&alg, key)?)` | `Key::new(&alg, key)?` |
| `SealingKey`, `OpeningKey`, `BoundKey`, `NonceSequence`, `nonce_sequence::{Counter32, Counter64}` and their builders | `Key`, given a `Nonce` per call from a sequence number the protocol keeps |
| `seal_in_place_append_tag(nonce, Aad::from(aad), in_out)` | `seal_in_place_append_tag(nonce, aad, in_out)`, with `aad: &[u8]` |
| `seal_in_place_separate_tag`, `open_in_place` | the same, with `aad: &[u8]` |
| `open_in_place_separate_tag(nonce, aad, tag, in_out)`, which ring takes as `(nonce, aad, tag, in_out, range)` | `open_in_place_separate_tag(nonce, aad, Tag::try_from(tag)?, ciphertext)` |
| `open_within(nonce, aad, in_out, range)` | `open_in_place` on the ciphertext's subslice, which leaves the plaintext there rather than moving it to the front |
| `Aad::from(aad)`, `Aad::empty()` | `aad`, `&[]` |
| `Nonce::assume_unique_for_key` | the same |
| `Nonce::try_assume_unique_for_key`, `Nonce::from` | `assume_unique_for_key`, given a `[u8; 12]` |
| `Tag`, ring's `Tag::try_from` | `Tag`, from `TryFrom<&[u8]>`, failing with `Error::WrongLength` |
| `Algorithm::{key_len, tag_len, nonce_len}` | the same |
| `NONCE_LEN`, `MAX_TAG_LEN`, `algorithm()` on each key | none; the `Algorithm` methods give each length |
| `AES_128_GCM`, `AES_192_GCM`, `AES_256_GCM`, `CHACHA20_POLY1305` | the same |
| `AES_128_GCM_SIV`, `AES_256_GCM_SIV` | none; [aws-lc-rs extras](quest/m3/parity/aws-lc-extras.md) |
| none | `gcm::Key::new(&cipher::AES_128, key, TagLength::Full)?`, for AES-GCM under an IV of any length, or with a tag cut to one of `TagLength`'s, as WebCrypto takes; its methods are `Key`'s, with an `Iv` for the nonce: `Iv::assume_unique_for_key(iv)?`, which refuses an empty IV |
| `RandomizedNonceKey::new(&AES_256_GCM, key)`, with 96-bit random nonces | `RandomizedNonceKey::new(&key)`, XChaCha20-Poly1305 with 192-bit random nonces, which never collide in practice |
| `RandomizedNonceKey::{seal_in_place_append_tag, open_in_place}` | the same, with the nonce a `RandomNonce` |
| `RandomizedNonceKey::seal_in_place_separate_tag` | none |
| `TlsRecordSealingKey`, `TlsRecordOpeningKey`, `TlsProtocolId` | `Key`; rind has no FIPS mode whose nonce rules they check |
| `open_separate_gather`, `seal_in_place_scatter`, `seal_out_of_place_scatter`, `prepare_nonce`, `SealingKeyPreparedNonce`, `OpeningKeyPreparedNonce`, `seal_in_place` (deprecated) | none |
| `chacha20_poly1305_openssh::{SealingKey, OpeningKey, KEY_LEN, TAG_LEN}` | none: only SSH transports use it, and rind has no SSH consumer |

### aead::quic

| aws-lc-rs | rind |
|---|---|
| `HeaderProtectionKey::new(&alg, key)`, `HeaderProtectionKey::from(okm)` | the same |
| `new_mask(sample)?` | `mask(&sample)`, which takes a `[u8; SAMPLE_LEN]` and cannot fail |
| `Sample`, `Algorithm::sample_len()` | `[u8; SAMPLE_LEN]`, `SAMPLE_LEN` |
| `Algorithm::key_len()`, `AES_128`, `AES_256`, `CHACHA20` | the same |
| `HeaderProtectionKey::algorithm()` | none |

## cipher

aws-lc-rs's `cipher` offers AES in several modes; rind's offers only what
protocols with their own integrity protection need. ring has none.

| aws-lc-rs | rind |
|---|---|
| `UnboundCipherKey::new(&AES_128, key)` and `EncryptingKey::ctr` or `DecryptingKey::ctr` | `AesCtr::new(&AES_128, key, 128)?`, whose last argument is how many of the counter block's rightmost bits count, as WebCrypto's `length` |
| `less_safe_encrypt(in_out, EncryptionContext::Iv128(iv))`, `decrypt` | `apply_keystream(&iv, in_out)?`, with `iv` the `[u8; 16]` counter block |
| `PaddedBlockEncryptingKey::cbc_pkcs7(key)` and `less_safe_encrypt(in_out, EncryptionContext::Iv128(iv))` | `AesCbcEncryptingKey::new(&AES_128, key)?` and `encrypt(CbcIv::assume_unpredictable(iv), in_out)`, which cannot fail |
| `PaddedBlockDecryptingKey::cbc_pkcs7(key)` and `decrypt(in_out, DecryptionContext::Iv128(iv))` | `AesCbcDecryptingKey::new(&AES_128, key)?` and `decrypt(&iv, in_out)?`, which clears `in_out` if the padding is malformed |
| `EncryptingKey::cbc`, `DecryptingKey::cbc`, unpadded | `encrypt_blocks(CbcIv::assume_unpredictable(iv), in_out)?` and `decrypt_blocks(&iv, in_out)?` on the keys above |
| `AES_128`, `AES_192`, `AES_256` | the same |
| `EncryptingKey::encrypt` and `PaddedBlockEncryptingKey::encrypt`, which pick a random IV | for CBC, `CbcIv::random()?`, read with `as_bytes` before encrypting; for CTR, pick the counter block with `rand::fill` |
| `DES_EDE3_FOR_LEGACY_USE_ONLY` and the other DES, the ECB, CFB, and OFB modes, `StreamingEncryptingKey`, `StreamingDecryptingKey` | none; [aws-lc-rs extras](quest/m3/parity/aws-lc-extras.md) |
| none | `Aes::new(&alg, key)?.encrypt_block(block)`, one AES block |
| none | `ChaCha20::new(&key).apply_keystream(nonce, counter, in_out)?` |

## agreement

| aws-lc-rs | rind |
|---|---|
| `EphemeralPrivateKey::generate(alg, rng)`, `PrivateKey::generate(alg)` | `PrivateKey::generate(&alg)?` |
| `compute_public_key()?` | `public_key()`, which cannot fail |
| `agree_ephemeral(key, &UnparsedPublicKey::new(alg, peer), err, kdf)` | `key.agree(peer)?`, returning a `SharedSecret` wiped on drop under `wipe`; run a KDF such as `hkdf` on it, as `kdf` did |
| `agree(&key, peer, err, kdf)` | `key.agree(peer)?`, which borrows the key, so it agrees again |
| `UnparsedPublicKey::new(alg, point)`, `ParsedPublicKey` of a point | `PublicKey::new(&alg, point)?`, which decompresses a compressed point, then `key.agree(peer.as_ref())`; `agree` alone takes an uncompressed point |
| `ParsedPublicKey` of a `SubjectPublicKeyInfo` | `PublicKey::from_spki(&alg, der)?`, which also takes WebCrypto's `id-ecDH` |
| `ParsedPublicKeyFormat` | none |
| `PublicKey`'s bytes | `PublicKey`'s bytes: an uncompressed point, or X25519's 32 bytes |
| `X25519`, `ECDH_P256`, `ECDH_P384`, `ECDH_P521` | the same |
| `PrivateKey::from_private_key(alg, bytes)` | `PrivateKey::from_scalar(&alg, bytes)` |
| `PrivateKey::from_private_key_der(alg, der)` | `from_pkcs8(&alg, der)` or `from_sec1(&alg, der)`, whichever the caller holds |
| `as_be_bytes()` to `EcPrivateKeyBin` or `Curve25519SeedBin` | `to_scalar()`, a `Scalar` wiped on drop under `wipe` |
| `AsDer<Pkcs8V1Der>::as_der()` | `to_pkcs8()`, which X25519 keys also have |
| `PublicKey::as_der()` | `PublicKey::to_spki()`, with an uncompressed point |
| `AsDer<EcPrivateKeyRfc5915Der>::as_der()`, `PublicKey::as_be_bytes()` | none; an ECDSA key pair's `to_sec1()` |
| `algorithm()` on each type | none |

`agree` refuses a compressed or DER-encoded peer key, which aws-lc-rs takes;
`PublicKey::new` and `from_spki` parse them first. Each refuses a hybrid
point, which aws-lc-rs takes and BoringSSL refuses.
X25519 keys load from and encode to PKCS#8 (RFC 8410), which aws-lc-rs's
agreement keys refuse.

## kem

| aws-lc-rs | rind |
|---|---|
| `DecapsulationKey::generate(&ML_KEM_768)` | the same |
| `encapsulation_key()?`, then `EncapsulationKey::key_bytes()?` | `public_key()`, and its bytes through `AsRef<[u8]>` |
| `EncapsulationKey::new(alg, bytes)`, `encapsulate()` | the same |
| `decapsulate(Ciphertext::from(bytes))` | `decapsulate(bytes)`, which borrows the key |
| `DecapsulationKey::new(alg, bytes)`, `DecapsulationKey::key_bytes()` | none: decapsulation keys are ephemeral |
| `ML_KEM_512`, `ML_KEM_1024` | none; [ML-KEM-512 and ML-KEM-1024](quest/m3/parity/ml-kem.md) |
| `algorithm()`, `Algorithm::id()`, `AlgorithmId`, `AlgorithmIdentifier` | none |

ring has no `kem`.

## signature

| aws-lc-rs | rind |
|---|---|
| `UnparsedPublicKey::new(alg, bytes).verify(m, s)` | `PublicKey::new(alg, bytes)?.verify(m, s)` |
| `UnparsedPublicKey::parse`, `ParsedPublicKey::new(alg, bytes)`, `verify_sig` | `PublicKey::new(alg, bytes)`, or `PublicKey::from_spki(alg, der)` for a `SubjectPublicKeyInfo`, then `verify` |
| `RsaPublicKeyComponents::verify(alg, m, s)`, `to_parsed_public_key(alg)` | `PublicKey::from_components(alg, &rsa::PublicKeyComponents { n, e })?.verify(m, s)` |
| `UnparsedPublicKey::verify_digest`, `ParsedPublicKey::verify_digest_sig`, `EcdsaKeyPair::sign_digest`, for ECDSA | `PublicKey::verify_digest`, `EcdsaKeyPair::sign_digest`, with SHA-256, SHA-384, or SHA-512; the digest's hash replaces the algorithm's, where aws-lc-rs refuses a mismatch |
| `verify_digest` and `sign_digest` for RSA, and `verify_digest` for Ed25519 | none: `Error::Unsupported` |
| `ParsedPublicKey::as_der()` | `PublicKey::to_spki()`, or a key pair's |
| `ParsedPublicKey::algorithm()` | none |
| `VerificationAlgorithm` trait, `EcdsaVerificationAlgorithm`, `EdDSAParameters` | `VerificationAlgorithm` |
| `RsaParameters` | `RsaVerificationAlgorithm`, which `PublicKey::new` also takes |
| `RSA_PSS_2048_8192_SHA256.with_pss_salt_length(RsaPssSaltLength::Custom(n))`, `Max`, and their SHA-384 and SHA-512 | `RsaVerificationAlgorithm::pss_sha256(RsaPssSaltLength::Custom(n))`, `Max`, and so on, which take the salt at run time too |
| `RSA_PSS_SHA256.with_pss_salt_length(..)` and their SHA-384 and SHA-512 | `RsaSigningAlgorithm::pss_sha256(..)` and so on |
| `RsaPssSaltLength::Digest` | `sign::RSA_PSS_SHA256`, `verify::RSA_PSS_SHA256`, and so on |
| OpenSSL's `RSA_PSS_SALTLEN_AUTO`, pyca's `PSS.AUTO` (not in aws-lc-rs) | `verify::RSA_PSS_SHA256_ANY_SALT` and so on |
| `RsaParameters::{public_modulus_len, min_modulus_len, max_modulus_len}` | none |
| `EcdsaSigningAlgorithm`, `RsaEncoding`, `RsaSignatureEncoding` | `EcdsaSigningAlgorithm`, `RsaSigningAlgorithm` |
| `ECDSA_P256_SHA256_ASN1_SIGNING` and the other `_SIGNING` | `sign::ECDSA_P256_SHA256_ASN1` |
| `ECDSA_P256_SHA256_ASN1`, `ED25519`, and the other verification constants | `verify::ECDSA_P256_SHA256_ASN1`, `verify::ED25519` |
| ECDSA signing, or `_FIXED`, with another SHA-2 hash than the curve's own | `sign_digest(&digest::digest(&SHA384, m))` and `verify_digest`, with the curve's own constant for the encoding |
| ECDSA with SHA-1, SHA-224, or SHA-3, or on secp256k1 (`P256K1`) | none; [aws-lc-rs extras](quest/m3/parity/aws-lc-extras.md) |
| `RSA_PKCS1_SHA256`, `RSA_PSS_SHA256`, and their SHA-384 and SHA-512 | `sign::RSA_PKCS1_SHA256`, `sign::RSA_PSS_SHA256`, and so on |
| `RSA_PKCS1_2048_8192_SHA256`, `RSA_PSS_2048_8192_SHA256`, and their SHA-384 and SHA-512 | `verify::RSA_PKCS1_SHA256`, `verify::RSA_PSS_SHA256`, and so on |
| `RSA_PKCS1_3072_8192_SHA384` | `verify::legacy::RSA_PKCS1_3072_SHA384` |
| `RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY`, `_SHA256_`, `_SHA512_` | `verify::legacy::RSA_PKCS1_1024_SHA1`, `RSA_PKCS1_1024_SHA256`, `RSA_PKCS1_1024_SHA512` |
| `RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY` | `verify::legacy::RSA_PKCS1_SHA1` |
| `KeyPair::public_key()`, ring's `RsaKeyPair::public()` | inherent `public_key()`, a `PublicKey`; `RsaKeyPair::public_key(&sign::X)` |
| `Ed25519PublicKey`, `EcdsaPublicKey`, `RsaSubjectPublicKey` | `PublicKey` |
| `generate_pkcs8(rng)`, `generate_pkcs8(alg, rng)`, `generate_pkcs8v1` | `generate(..)?.to_pkcs8()` |
| `EcdsaKeyPair::from_pkcs8(alg, der)`, ring's `(alg, der, rng)` | `from_pkcs8(&alg, der)` |
| `EcdsaKeyPair::from_private_key_and_public_key`, ring's with an `rng` | `from_scalar_and_public_key(&alg, scalar, public_key)`, with no random source |
| `EcdsaKeyPair::from_private_key_der` | `from_sec1`, which refuses PKCS#8 |
| `RsaKeyPair::from_der` | `from_pkcs1` |
| `RsaKeyPair::from_components`, `KeyPairComponents` | none: load the key as PKCS#1 or PKCS#8 |
| `Ed25519KeyPair::from_pkcs8_maybe_unchecked` | `from_pkcs8`, which takes v1 and v2 |
| `Ed25519KeyPair::from_seed_unchecked` | `from_seed`, or `from_seed_and_public_key`, which checks the public key |
| `to_pkcs8()`, `to_pkcs8v1()`, `public_key().as_der()`, each an allocated `Document` | `to_pkcs8()`, `to_pkcs8v1()` (Ed25519), `to_spki()`, each of fixed capacity; `Pkcs8` is wiped on drop under `wipe` |
| `EcdsaKeyPair::private_key().as_der()` | `to_sec1()`, an `encoding::Sec1` wiped on drop under `wipe` |
| `EcdsaKeyPair::sign(rng, m)`, `RsaKeyPair::sign(alg, rng, m, &mut sig)`, `Ed25519KeyPair::try_sign` | `sign(m)`, `sign(alg, m)`, which take no random source and return a `Signature` |
| `rsa::KeySize`, `RsaKeyPair::generate(size)` | the same; `KeySize` adds `Rsa6144` |
| `EcdsaKeyPair::private_key().as_be_bytes()` (not in ring) | `to_scalar()`, an `EcdsaScalar` wiped on drop under `wipe` |
| `Ed25519KeyPair::seed()?.as_be_bytes()` (not in ring) | `to_seed()`, an `Ed25519Seed` wiped on drop under `wipe` |
| `public_modulus_len()`, `algorithm()`, `generate_fips` | none |
| `ED25519_PUBLIC_KEY_LEN` | none: always 32 |
| `rsa::PublicKey::from_der` | `PublicKey::new(&verify::RSA_PKCS1_SHA256, der)`, for one algorithm and PKCS#1 or `SubjectPublicKeyInfo` DER |
| `rsa::PublicKey::{modulus, exponent, modulus_len}`, `PublicKeyComponents::from(&key)` | none |
| `PqdsaKeyPair::generate(&ML_DSA_65_SIGNING)` | `sign::MlDsaKeyPair::<MlDsa65>::generate()`, whose parameter set is a type |
| `PqdsaKeyPair::from_seed(&alg, seed)`, `from_pkcs8(&alg, der)` | `MlDsaKeyPair::<P>::from_seed(seed)`, `from_pkcs8(der)`, which takes the seed, expanded, and both forms |
| `PqdsaKeyPair::to_pkcs8v1()`, `to_pkcs8()` | `to_pkcs8()`, the seed form, or the expanded form for a key loaded without its seed, where aws-lc-rs fails |
| `PqdsaKeyPair::sign(m, &mut sig)` | `sign(m)`, returning an `MlDsaSignature<P>` of the set's fixed length |
| `PqdsaKeyPair::from_raw_private_key`, `private_key().as_raw_bytes()` | none: load the expanded key as PKCS#8 |
| `ML_DSA_44`, `ML_DSA_65`, `ML_DSA_87` for verification | `verify::ML_DSA_44`, `ML_DSA_65`, `ML_DSA_87`, with `PublicKey::new` (the raw key) or `from_spki` |

`PublicKey::new` refuses a compressed ECDSA point and an ECDSA, Ed25519, or
ML-DSA `SubjectPublicKeyInfo`, which aws-lc-rs takes. `PublicKey::from_spki` takes
the latter, with its point compressed or not, and
`agreement::PublicKey::new` decompresses a bare point. It takes an RSA key as
PKCS#1 or as a `SubjectPublicKeyInfo`, as aws-lc-rs does, but refuses the
latter's algorithm (`rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa`) with
parameters other than `NULL` or none, which aws-lc ignores, and an RSA key's bytes are always its PKCS#1 DER.
It also refuses an Ed25519 key of small order, as libsodium does, which
aws-lc-rs and ring take: with the identity as the key, `R` the identity and
`S = 0` verify any message. No honest key has small order.

An ECDSA key pair's loaders take its public key uncompressed or compressed,
as aws-lc-rs does, but refuse a hybrid point, which aws-lc-rs takes; ring,
and so rind-ring, takes only the uncompressed one.
`from_scalar_and_public_key` refuses a scalar that is not exactly the
curve's length, as ring does, where aws-lc-rs takes leading zeros added or
stripped.

Every private key loader refuses bytes after the encoded key, which
aws-lc-rs ignores and ring refuses. The ECDSA and RSA PKCS#8 loaders take
version 1 only, as ring does, and the Ed25519 one also takes version 2 with
its public key. Each refuses version 2 without a public key, which aws-lc-rs
takes: RFC 5958 sets version 2 only when the public key is present.

## rsa

rind signs and verifies with RSA through `signature`, and encrypts with
RSA-OAEP through `rsa`. ring has no RSA encryption.

| aws-lc-rs | rind |
|---|---|
| `PrivateDecryptingKey`, then `OaepPrivateDecryptingKey::new(key)` | `DecryptingKey`, which decrypts OAEP itself |
| `PublicEncryptingKey`, then `OaepPublicEncryptingKey::new(key)` | `EncryptingKey`, which encrypts OAEP itself |
| `PrivateDecryptingKey::from_pkcs8(der)`, `generate(size)`, `as_der()` | `DecryptingKey::from_pkcs8(alg, der)`, `from_pkcs1(alg, der)`, `generate(alg, size)`, `to_pkcs8()`, each key bound to one algorithm |
| `PrivateDecryptingKey::public_key()` | `public_key()`, an `EncryptingKey` bound to the same algorithm; `to_spki()` for its `SubjectPublicKeyInfo` |
| `PublicEncryptingKey::from_der(spki)` | `EncryptingKey::new(alg, der)`, which takes a `SubjectPublicKeyInfo` or PKCS#1 `RSAPublicKey`, or `EncryptingKey::from_components(alg, &PublicKeyComponents { n, e })` |
| `PublicEncryptingKey::as_der()` | `EncryptingKey::to_spki()` |
| `OAEP_SHA256_MGF1SHA256`, `OAEP_SHA384_MGF1SHA384`, `OAEP_SHA512_MGF1SHA512` | `OAEP_SHA256`, `OAEP_SHA384`, `OAEP_SHA512` |
| `OAEP_SHA1_MGF1SHA1` | `legacy::OAEP_SHA1` |
| `encrypt(alg, m, &mut out, label)`, `decrypt(alg, c, &mut out, label)` | `encrypt(m, label)`, `decrypt(c, label)` with the key's algorithm, returning a `Ciphertext` or a `Plaintext`, which is not wiped on drop; `None` for the label is `b""` |
| `max_plaintext_size(alg)` | `max_message_len()` |
| `ciphertext_size()`, `min_output_size()`, `key_size_bytes()`, `key_size_bits()`, `EncryptionAlgorithmId`, `OaepAlgorithm::id()` | none |
| `Pkcs1PublicEncryptingKey`, `Pkcs1PrivateDecryptingKey` | none: PKCS#1 v1.5 encryption invites padding-oracle attacks |

Every RSA-OAEP decryption failure, a ciphertext of the wrong length, not
below the modulus, or with bad padding, is `Error::DecryptFailed`, as
aws-lc-rs's is `Unspecified`. Both refuse keys below 2048 bits.
`EncryptingKey::new` refuses a `SubjectPublicKeyInfo` as `PublicKey::new`
does: with parameters other than `NULL` or none, or bytes after it.

## constant_time

| aws-lc-rs | rind |
|---|---|
| `verify_slices_are_equal(a, b)` | `verify(a, b)`, failing with `Error::WrongLength` for unequal lengths and `Error::NotEqual` for unequal contents |

## rand

No rind call takes a random source, so there is nothing to pass one to.

| aws-lc-rs | rind |
|---|---|
| `SystemRandom::new().fill(out)`, `rand::fill(out)` | `rand::fill(out)` |
| `generate::<[u8; N]>(rng)?.expose()` | `rand::fill` into a `[u8; N]` |
| `SecureRandom`, `RandomlyConstructable`, `Random` | none |

## error

aws-lc-rs's `error::Unspecified` and `error::KeyRejected` become one
`rind::Error`, whose variant depends on the kind of call. ring's names match.
`Error` is `#[non_exhaustive]`, so a `match` on it needs a wildcard arm.

| aws-lc-rs | rind |
|---|---|
| `KeyRejected`, from loading a key pair | `Error::KeyRejected` |
| `Unspecified`, from a peer's or public key that is malformed, off the curve, or the wrong length | `Error::KeyRejected`, from `PublicKey::new`, `agree`, or `EncapsulationKey::new` |
| `KeyRejected::description_()` | `KeyRejected`'s `Display` |
| `Unspecified`, from `verify`, `hmac::verify`, or `pbkdf2::verify` | `Error::BadSignature` |
| `Unspecified`, from `open_in_place` | `Error::DecryptFailed` |
| `Unspecified`, from a symmetric key, nonce, tag, or output of the wrong length | `Error::WrongLength` |
| `Unspecified`, from `SystemRandom::fill` or `generate` | `Error::RngFailed` |
| `Unspecified`, from `constant_time::verify_slices_are_equal` | `Error::NotEqual` |
| `Unspecified`, from RSA signing or ECDH when an internal check fails | `Error::Fault` |
| `Unspecified`, from `sign_digest` or `verify_digest` with a digest's hash or key the call does not take | `Error::Unsupported` |

## cpu

ring and aws-lc-rs detect CPU features and fall back to slower code, down
to portable C. rind picks its path per CPU too, but only down to a floor (see
[PLATFORMS.md](PLATFORMS.md)): it panics on a CPU below it.

| aws-lc-rs | rind |
|---|---|
| none | `cpu::check()`, at startup, returns `cpu::MissingFeature` naming the feature |
| none | `cpu::has_aes_hardware()`, for preferring ChaCha20-Poly1305 where AES runs in software |

## key_wrap

ring has none.

| aws-lc-rs | rind |
|---|---|
| `AesKek::new(&AES_128, key)?`, `AES_128`, `AES_256` | the same |
| none | `AES_192` |
| `KeyWrap::wrap(kek, key, output)?`, which consumes the key and takes any longer `output` | `kek.wrap(key, wrapped)?`, which borrows it and takes `wrapped` exactly 8 bytes longer than `key` |
| `KeyWrap::unwrap(kek, wrapped, output)?` | `kek.unwrap(wrapped, key)?`, with `key` exactly 8 bytes shorter than `wrapped`, cleared if it fails to verify |
| `KeyWrapPadded::wrap_with_padding(kek, key, output)?`, which takes any `output` at least 15 bytes longer than `key` | `kek.wrap_padded(key, wrapped)?`, with `wrapped` exactly `key.len().next_multiple_of(8) + 8` bytes |
| `KeyWrapPadded::unwrap_with_padding(kek, wrapped, output)?` | `kek.unwrap_padded(wrapped, key)?`, with `key` exactly 8 bytes shorter than `wrapped`, cleared if it fails to verify; both return the key |
| `BlockCipherId`, `AesKek::block_cipher_id()` | none |

## Other modules

| aws-lc-rs | rind |
|---|---|
| `cmac`, `kdf` (KBKDF and SSKDF), `tls_prf` | none; [aws-lc-rs extras](quest/m3/parity/aws-lc-extras.md) |
| `pkcs8::Document` | `encoding::Pkcs8`, `encoding::Spki` |
| `encoding`'s `AsDer`, `AsBigEndian`, and `AsRawBytes` | `to_pkcs8()` and `to_spki()`; an ECDSA key pair's `to_sec1()` and `to_scalar()`, and an Ed25519 key pair's `to_pkcs8v1()` and `to_seed()`; other raw keys none |
| `io::Positive`, `io::der`, `iv::FixedLength`, `test`, `test_file!`, `unstable`, and ring's `deprecated_test` | none |
| `init`, `try_fips_mode`, `fips_mode`, `try_fips_self_test`, `fips_version`, `try_fips_cpu_jitter_entropy`, `fips_cpu_jitter_entropy`, `awslc_version` | none: rind has no C library to initialize and no FIPS module |

## Adapter crates

Each `rind-*` crate stands in for a crate's aws-lc-rs or ring backend. rind
panics on a CPU missing a feature it requires, so every adapter function
that returns a provider refuses one with the adapter's own
`MissingFeature` instead, which displays rind's message. rind-rustls, whose
signatures are rustls's provider's, does not. rind-ring, whose signatures
are ring's, and rind-rcgen's `KeyPair`, whose errors are rcgen's, cannot.
Call `rind::cpu::check()` before using them.

### rind-ring

rind-ring offers ring 0.17's API name for name, so a crate on ring swaps it
in with `ring = { package = "rind-ring", version = "0.17" }` and no code
changes. The rename reaches only that crate. A binary moves every crate in
its tree on ring 0.17, such as rustls or quinn-proto on their `ring`
features, by adding `[patch.crates-io] ring = { git =
"https://github.com/moq-dev/rind-patch" }` to its workspace's root
`Cargo.toml` and running `cargo update -p ring`. That builds
[rind-patch](https://github.com/moq-dev/rind-patch)'s unpublished crate named
`ring`, which re-exports rind-ring, and `cargo tree -i ring` then prints only
`ring v0.17.999` from rind-patch. It panics wherever ring
panics, so its signatures stay ring's, and adds nothing to ring's API. Its [README](rind-ring/README.md) lists the
items it leaves out and the inputs it refuses where ring takes them.

### rind-aws-lc-rs

rind-aws-lc-rs offers aws-lc-rs 1.x's API name for name for every item rind
backs, so a crate on aws-lc-rs swaps it in with `aws-lc-rs = { package =
"rind-aws-lc-rs", version = "1" }` and no code changes. The rename reaches
only that crate. It accepts every aws-lc-rs feature but `fips`, and adds only
a `wipe` feature, since aws-lc-rs always wipes. Its [README](rind-aws-lc-rs/README.md) lists
the items it leaves out, such as ML-KEM-512 and ML-KEM-1024,
`PqdsaPrivateKey::as_raw_bytes`, SHA-224, and the PKCS#1 v1.5 encryption keys,
and where it behaves differently. It offers ML-DSA
(`signature::{ML_DSA_44, ML_DSA_65, ML_DSA_87}`, `PqdsaKeyPair`, and the other
`Pqdsa*` types except `as_raw_bytes`). rustls-webpki's `aws-lc-rs` feature and
rcgen's `aws_lc_rs` feature build on it. rustls's `aws_lc_rs` provider still
names `tls_prf`, and from 0.23.46 also `kem::ML_KEM_1024`, so it does not
build yet.

### rind-rustls

rind-rustls offers rustls's `crypto::aws_lc_rs` API item for item, so
replacing that path with `rind_rustls` changes no other code. It leaves out
what rind cannot back yet; see [rustls provider parity](quest/m3/parity/rustls.md).

| rustls `crypto::aws_lc_rs` | rind-rustls |
|---|---|
| `kx_group::MLKEM1024`, in `ALL_KX_GROUPS` | none |
| ML-DSA, which `default_provider()` verifies and signs with | none |

Its [README](rind-rustls/README.md) lists where it behaves differently, such
as its cipher suite order.

### rind-rcgen

`rind_rcgen::KeyPair` offers `rcgen::KeyPair`'s API as rcgen's default `ring`
backend builds it, so code swaps the type in unchanged. It signs with ECDSA
P-256 and P-384, Ed25519, and RSA with PKCS#1 v1.5, loading only PKCS#8 keys
and generating no RSA keys. Its [README](rind-rcgen/README.md) lists what it
leaves out, such as P-521, which rcgen names only with its `aws_lc_rs` feature.

Without rcgen's `crypto` feature, rcgen needs each certificate's
`serial_number` set, and writes key identifiers only when
`key_identifier_method` is set, such as to `KeyIdMethod::PreSpecified` with
the first 20 bytes of the SHA-256 of `key.subject_public_key_info()`, which is
what rcgen's default `KeyIdMethod::Sha256` computes.

### rind-dimpl, rind-str0m, rind-object-store, and rind-jsonwebtoken

| aws-lc-rs backend | rind |
|---|---|
| dimpl's `crypto::aws_lc_rs::default_provider()` | `rind_dimpl::default_provider()` |
| str0m's default `aws-lc-rs` feature, or `str0m_aws_lc_rs::default_provider()` | `default-features = false`, with `set_crypto_provider(Arc::new(rind_str0m::default_provider()))` |
| `str0m_aws_lc_rs::dimpl_crypto_provider()` | `rind_str0m::dimpl_crypto_provider()` |
| object_store's `aws`, `azure`, and `gcp` features | the `*-base` features, with `with_crypto_provider(rind_object_store::default_provider())` |
| jsonwebtoken's `crypto::aws_lc::DEFAULT_PROVIDER` | `rind_jsonwebtoken::DEFAULT_PROVIDER` |

### rind-openmls

rind-openmls offers openmls_rust_crypto's API, item for item, so only the
dependency and its `use` lines change. It offers the same ciphersuites; its
[README](rind-openmls/README.md) lists the draft features rind cannot back.

| openmls_rust_crypto | rind |
|---|---|
| `OpenMlsRustCrypto`, `RustCrypto`, `RandError`, `MemoryStorage`, `MemoryStorageError` | the same names in `rind_openmls` |
| the `test-utils` and `extensions-draft` features | the same features |

## Crates with their own crypto backend

Surveyed on 2026-10-31 against each crate's latest release, by reading its
features and source; none were built. A migrated graph should give no output
from `cargo tree -e normal,build -i ring` or `-i aws-lc-sys`, except
`ring v0.17.999` from rind-patch under the ring patch.

"Install" means calling `rind_rustls::default_provider().install_default()`
before the crate builds its TLS config. Crates that read rustls's process
default panic without one, and a few (jsonrpsee, pingora, tauri on mobile)
install ring's if nothing is installed first.

- **rind-rustls**: TLS runs through rustls. Pick the listed features and
  install or pass rind-rustls's provider.
- **rind-x**: an existing adapter crate covers it.
- **Pure Rust**: its default build, or the listed features, use neither.
- **Patch**: ring 0.17 is hard-wired, and a binary moves it with the
  [ring patch](#rind-ring). Built against the patch on 2026-11-06, with no
  other ring left in the tree.
- **Adapter**: a new `rind-*` crate could cover it through a public hook.
  [Adapters](#adapters) says which are worth building.
- **Unsupported**: aws-lc-rs, ring 0.16, or a ring item rind-ring leaves out
  is hard-wired. The cell names the alternative or the upstream change that
  would fix it.

### TLS and HTTP

| Crate | What ties it | On rind |
|---|---|---|
| rustls 0.23 | `ring` and `aws_lc_rs` features pick a provider | **rind-rustls**: `default-features = false`, `std`, `tls12` |
| rustls-webpki 0.103 | `ring` and `aws-lc-rs` fill `ALL_VERIFICATION_ALGS` | **rind-rustls**: no features; direct callers pass `rind_rustls::default_provider().signature_verification_algorithms.all` |
| rustls-platform-verifier 0.7 | none | **rind-rustls**: `Verifier::new(provider)` |
| tokio-rustls 0.26, futures-rustls 0.26 | default `aws_lc_rs` | **rind-rustls**: `default-features = false`, `logging`, `tls12` |
| hyper-rustls 0.27 | default `aws-lc-rs` | **rind-rustls**: `default-features = false` and a `with_provider_and_*` builder; `with_native_roots()` and its siblings need ring or aws-lc-rs |
| reqwest 0.13 | default `rustls` is aws-lc-rs | **rind-rustls**: `rustls-no-provider`, install. `http3` always enables aws-lc-rs |
| ureq 3 | default `rustls` is ring | **rind-rustls**: `rustls-no-provider` (marked unstable) and `rustls-webpki-roots`, or `platform-verifier` with the agent's roots set to `RootCerts::PlatformVerifier`, install |
| axum-server 0.8 | `tls-rustls` is aws-lc-rs | **rind-rustls**: `tls-rustls-no-provider`, install |
| actix-web 4, actix-tls 3, awc 3 | none | **rind-rustls**: `rustls-0_23`, with a server config built on rind-rustls; awc's default client needs `rustls-0_23-webpki-roots` or `rustls-0_23-native-roots`, install |
| tonic 0.14 | `tls-ring`, `tls-aws-lc` | **rind-rustls**: `tls-native-roots` or `tls-webpki-roots` alone (a server-only build needs `_tls-any`), install |
| tungstenite 0.30, tokio-tungstenite 0.30 | none | **rind-rustls**: a `rustls-tls-*-roots` feature, install |
| tokio-websockets 0.13 | handshake SHA-1 from ring, aws-lc-rs, or OpenSSL | **rind-rustls**: `sha1_smol` and `rustls-bring-your-own-connector` |
| lettre 0.11 | `rustls-tls` is ring | **rind-rustls**: `rustls-no-provider`, install |
| kube 4 | default `rustls-tls` with `ring` | **rind-rustls**: `client` and `rustls-tls`, install. `oidc` and `oauth` need **Patch** |
| async-nats 0.51 | default `ring`; `crypto` hashes with it | **rind-rustls**: without `ring`, `crypto`, or `object-store`, install; with them, **Patch** |
| mysql_async 0.37 | `default-rustls` is aws-lc-rs | **rind-rustls**: `default-rustls-no-provider`, install |
| tokio-postgres-rustls 0.14 | optional, off by default | **rind-rustls**: default features |
| bollard 0.21 | `ssl` is ring | **rind-rustls**: `ssl_providerless`, install |
| ldap3 0.12 | `tls-rustls-*`; `gssapi` and `ntlm` call ring | **rind-rustls**: `tls-rustls` and `rustls-provider`, install; not `gssapi` or `ntlm` |
| metrics-exporter-prometheus 0.18 | `push-gateway` is aws-lc-rs | **rind-rustls**: `push-gateway-no-tls-provider`, install |
| tauri 2 | mobile `rustls-tls` installs ring | **rind-rustls**: desktop needs nothing; mobile skips `rustls-tls`; tauri-plugin-http goes through reqwest 0.12's `rustls-tls-native-roots-no-provider` |
| AWS SDK: aws-config 1, aws-smithy-http-client 1 | `default-https-client` is aws-lc-rs; the legacy `rustls` default is ring | **rind-rustls** only under `--cfg aws_sdk_unstable`, through `CryptoMode::Custom`; otherwise Adapter. Request signing (aws-sigv4) is pure Rust |
| poem 3 | `rustls` calls aws-lc-rs; `acme*` calls ring | Adapter: a TLS `Acceptor` over tokio-rustls |
| sqlx 0.9 | `tls-rustls-*` hard-code ring's or aws-lc-rs's provider | **Patch**: `tls-rustls-ring-webpki` or `tls-rustls-ring-native-roots` |
| mongodb 3 | default `rustls-tls` hard-codes ring's provider | **Patch** |
| fred 10 | rustls only behind `enable-rustls` (aws-lc-rs) or `enable-rustls-ring` | **Patch**: `enable-rustls-ring` |
| rskafka 0.6 | `transport-tls` enables ring | **Patch** |
| jsonrpsee 0.26 | `tls` enables and installs ring | **Patch** |
| pingora 0.9 | pingora-rustls depends on ring | **Patch**: `rustls` |
| tiny_http 0.12 | `ssl-rustls` is rustls 0.20 | Unsupported over TLS |
| webpki 0.22 | calls ring's `io` DER reader, which rind-ring leaves out | Unsupported: legacy; move to rustls 0.23 and rustls-webpki |
| sct 0.7 | ring, unconditionally | **Patch** |

### QUIC, WebRTC, and peer-to-peer

| Crate | What ties it | On rind |
|---|---|---|
| quinn 0.11, quinn-proto 0.11, h3-quinn | `rustls` is an alias for `rustls-ring`; the Retry tag, reset key, and token key call ring or aws-lc-rs | **Patch**: the default `rustls-ring`, or noq on rind-rustls |
| noq 1.4 | default `ring` | **rind-rustls**: `rustls` without `ring`, plus the caller's `HmacKey` and `HandshakeTokenKey` on rind's HMAC, HKDF, and AES-256-GCM |
| iroh 1.4 | default `tls-ring` picks the provider | **rind-rustls**: `default-features = false`, `Endpoint::builder().crypto_provider(..)`. iroh-relay's `server` enables ring |
| wtransport 0.7 | needs `ring` or `aws-lc-rs`, and quinn's defaults | **Patch**: the default `ring` |
| s2n-quic 1 | s2n-quic-crypto always links aws-lc-rs | Unsupported |
| quiche 0.30 | BoringSSL | Unsupported: C |
| dimpl 0.9 | default aws-lc-rs | **rind-dimpl** |
| str0m 0.25 | default aws-lc-rs | **rind-str0m** |
| webrtc 0.21 (rtc 0.21) | default `crypto-ring`, or `crypto-aws-lc-rs` | **Patch**: the default `crypto-ring` |
| webrtc-dtls 0.12, stun 0.17, turn 0.17 | ring, unconditionally | **Patch** |
| libp2p-tls 0.7, libp2p-quic 0.14, libp2p-noise 0.47 | aws-lc-rs and ring, unconditionally | Unsupported: needs a provider hook upstream |
| snow 0.10 | opt-in `ring-resolver` | **Pure Rust** by default. Adapter through `CryptoResolver`, once rind loads static X25519 keys |
| boringtun 0.7 | ring's ChaCha20-Poly1305 and constant-time comparison | **Patch** |

### DNS

| Crate | What ties it | On rind |
|---|---|---|
| hickory-proto, hickory-net, hickory-resolver 0.26 | TLS, HTTPS, and QUIC need a `*-ring` or `*-aws-lc-rs` feature; DNSSEC validation calls them internally | **Patch**: the `*-ring` features. Plain DNS is unaffected |
| domain 0.12 | DNSSEC and TSIG need ring or OpenSSL | **Patch**: `ring`, `tsig`, and `unstable-validator`. `unstable-sign` builds RSA keys from components, which rind-ring leaves out |

### Certificates, ACME, and tokens

| Crate | What ties it | On rind |
|---|---|---|
| rcgen 0.14 | default `ring`, or `aws_lc_rs`, gates `KeyPair` | **rind-rcgen**: ECDSA P-256 and P-384, Ed25519, and loaded RSA keys. Without rcgen's `crypto` feature, set each certificate's serial number, and its `key_identifier_method` or the key identifiers are empty |
| instant-acme | 0.8 calls aws-lc-rs or ring; the unreleased 0.9 takes a `CryptoProvider` | Unsupported: 0.8 has no provider hook, and 0.9 is unreleased |
| rustls-acme 0.15, tokio-rustls-acme 0.9 | account keys and CSRs call ring or aws-lc-rs | **Patch**: rustls-acme's `ring` without its default `aws-lc-rs` |
| x509-parser 0.18 | `verify` is ring, `verify-aws` aws-lc-rs | **Patch**: `verify`, or verify `tbs_certificate` with `rind::signature` |
| x509-certificate 0.25, cryptographic-message-syntax 0.28 | ring types in their public API | **Patch** |
| sigstore 0.14, tough 0.24 | aws-lc-rs, unconditionally | Unsupported |
| jsonwebtoken 11 | optional `aws_lc_rs` | **rind-jsonwebtoken**, every algorithm. `rust_crypto` is the pure-Rust alternative |
| jwtk 0.5 | default `aws-lc` for RSA verification and JWK conversion | Adapter, for caller-held keys only |
| biscuit 0.8, rusty_paseto 0.10 | ring, unconditionally | **Patch** |
| paseto 2 | ring 0.16 and OpenSSL | Unsupported |
| passkey 0.6 (passkey-crypto) | optional `aws-lc-rs` | **Pure Rust** by default |
| tame-oauth 0.10 | `jwt` is ring | **Patch** |
| gcp_auth 0.12 | default `ring` for TLS and service-account signing | **rind-rustls** without `ring` or `aws-lc-rs`; service-account keys need **Patch** with the default `ring` |
| google-cloud-auth 1 | defaults are aws-lc-rs | **rind-rustls**: `default-features = false`, install; signing loads keys through the installed provider. `idtoken` also installs rind-jsonwebtoken |
| yup-oauth2 12 | default `ring` for TLS and service-account signing | **rind-rustls** for user flows, through `with_client` and hyper-rustls; service accounts need **Patch** with the default `ring` |
| matrix-sdk-crypto 0.19 | opt-in `rust-x509-verifier-impl` | **Pure Rust** without it |

### Storage, databases, and other

| Crate | What ties it | On rind |
|---|---|---|
| object_store 0.14 | `aws`, `gcp`, `azure` and `http` enable aws-lc-rs | **rind-object-store**, with the `*-base` features; HTTPS through reqwest on rind-rustls |
| parquet 60 | `encryption` calls ring | **Patch** |
| russh 0.65 | default `aws-lc-rs`, or `ring`, for its AES-GCM and ChaCha20-Poly1305 transport | Unsupported: its cipher trait is private, and its `ring` calls `chacha20_poly1305_openssh`, which rind refuses |
| scram 0.6 | ring 0.16, unconditionally | Unsupported |
| ethereum_hashing 0.8 | default `ring` for SHA-256 | **Pure Rust** on x86_64; other targets need ring |
| openmls 0.9 | a provider crate, openmls_rust_crypto or openmls_libcrux_crypto | **rind-openmls**, in place of openmls_rust_crypto |

## Adapters

No new adapter is planned (maintainer, 2026-10-31):

- **quinn**: its rustls integration cannot be built without ring or
  aws-lc-rs, so an adapter would carry its own port of quinn's
  `crypto::rustls` session. The ring patch moves quinn as it is, and noq,
  quinn's fork, already runs on rind-rustls.
- **webrtc**: `rtc_crypto::RTCCryptoProvider` covers all of its crypto, and
  rind lacks only the AES-CCM DTLS suites, but no consumer asks for it.

Nor are these worth a crate:

- **AWS SDK**: the adapter would be a whole HTTP client; stabilizing
  `CryptoMode::Custom` upstream needs none.
- **snow**: its default backend is already pure Rust, and rind cannot yet
  load a static X25519 key or hash with BLAKE2.
- **poem** and **jwtk**: each is a few lines of the caller's code over
  tokio-rustls or rind's signatures.
