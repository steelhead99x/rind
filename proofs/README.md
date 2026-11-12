# Proofs of rind's Rust

Lean proofs that rind's own Rust computes its specified result, composed with
the published proofs of the routines it imports, so that an operation's whole
computation is proven. [Charon](https://github.com/AeneasVerif/charon) and
[Aeneas](https://github.com/AeneasVerif/aeneas) translate the Rust to Lean, and
the theorems are about that translation.

`nix develop .#prove --command admin/prove` translates the Rust and checks
every proof against the translation, after the HOL Light proofs below and
`admin/prove bytes`, which checks that each imported routine those proofs
build on, from s2n-bignum, Vale, and aws-lc, is in rind's build the object
code its own proof is about. The `prove` workflow runs it nightly and on pull
requests that change rind's source or these files.

## HOL Light proofs

`hol-light/<arch>/` holds rind's own [HOL Light](https://hol-light.github.io/)
proofs of the `asm!` blocks it runs, for routines whose published proofs do
not cover them, on [s2n-bignum](https://github.com/awslabs/s2n-bignum)'s
instruction models, tactics, and specs at the commit of rind's
`thirdparty/s2n-bignum` submodule, the revision rind's transliteration pins.
Each proof's object code is the block's bytes as rind's release build emits
them, which `admin/prove` extracts, so no transliteration is trusted: the
proof lists the bytes and fails unless the build's are the same. An axiom in
`Rind/<Arch>/` that restates one of these theorems names the file, whose
revision is rind's commit. `nix develop .#hol-light --command admin/prove
hol-light` checks them alone, in nixpkgs' HOL Light.

- `aarch64/bignum_eq.ml`: `BIGNUM_EQ_CORRECT`, s2n-bignum's proof of
  `bignum_eq` on the block in `low::aarch64::bignum_eq::bignum_eq`, which is
  s2n-bignum's routine without its `ret`.
- `aarch64/sha256_block_data_order_hw.ml`: `SHA256_HW_SUBROUTINE_CORRECT`,
  rind's proof that the naked function
  `low::aarch64::sha256::sha256_block_data_order_hw`, aws-lc's routine for
  the SHA-256 instructions, computes s2n-bignum's FIPS 180-4 spec,
  `sha256_hash_blocks`. A naked function's object code is its whole section
  with its relocations and the read-only data they reach, here the round
  constants, which `admin/prove` extracts as an object file; the proof checks
  the constants against FIPS 180-4's.
- `<arch>/ct_compare_16.ml` and `<arch>/ct_compare_bytes.ml`, on x86_64 and
  aarch64: `CT_COMPARE_16_CORRECT` and `CT_COMPARE_BYTES_CORRECT`, that the
  blocks in `low::<arch>::cpu::ct_compare_16` and `ct_compare_bytes` return
  zero exactly when their inputs are equal, and `CT_COMPARE_16_SAFE` and
  `CT_COMPARE_BYTES_SAFE`, in s2n-bignum's style, that their trace of loads
  and branches is a function of the addresses and length alone, each load in
  bounds. Both functions are `#[inline(never)]` with fixed registers, so the
  proof covers their one copy.

`hol-light/s2n-bignum/` holds what these proofs add to s2n-bignum, ahead of
the submodule on HOL Light's load path: specs from s2n-bignum pull requests
not yet merged, and `x86.patch`, rind's additions to the x86 model, which
`x86-cosim.ml` checks against the CPU. Its
[README](hol-light/s2n-bignum/README.md) lists each, so they can be offered
upstream. `nix develop .#hol-light --command admin/prove cosim` runs the
cosimulation, on an x86_64 CPU with AVX2.

## What is proven

X25519 on x86_64 and aarch64, from the agreement API's `PrivateKey` to
s2n-bignum's routines, in `Rind/X86_64/X25519.lean`, which `admin/prove` also
writes for aarch64:

- `x25519_generate`: the key's scalar is the 32 drawn bytes, read
  little-endian, it holds its public key, and a failed draw is refused;
- `x25519_from_scalar`: a loaded key's scalar is the 32 given bytes, read
  little-endian, it holds its public key, and any other length is refused;
- `x25519_public_key`: the public key a key holds is the 32 little-endian
  bytes of `rfcx25519(scalar, 9)`;
- `x25519_agree`: a peer key that is not 32 bytes is refused, so is an
  all-zero result, and otherwise the secret is the 32 little-endian bytes of
  `rfcx25519(scalar, u)`, for the peer's bytes `u` read little-endian;
- `x25519_shared_secret`: the secret's bytes are those.

`rfcx25519` is HOL Light's RFC 7748 X25519, clamping and masking included.

P-256 ECDH on aarch64, from the same `PrivateKey` to s2n-bignum's routines, in
`Rind/Aarch64/P256.lean`:

- `p256_generate`: the key's scalar is the first of up to 64 draws whose
  bytes, read big-endian, are in [1, n), it holds its public key, and the key
  is refused if a draw fails before one is, or none is;
- `p256_from_scalar`: a loaded key's scalar is the 32 given bytes, read
  big-endian, refused unless they are 32 bytes and in [1, n), and it holds
  its public key;
- `p256_public_key`: the public key a key holds is the X9.62 uncompressed
  encoding of the scalar times G;
- `p256_agree`: a peer key is refused unless it is a 65-byte uncompressed
  point whose coordinates are below p and on the curve, and otherwise the
  secret is the 32 big-endian bytes of the x-coordinate of the scalar times
  that point, or a fault unless that is a finite point on the curve;
- `p256_shared_secret`: the secret's bytes are those.

`p256Pow` is HOL Light's `group_pow p256_group`, defined as HOL Light does,
and `Rind/P256Group.lean` proves it is multiplication in Mathlib's group of
points on the curve. `Rind/P256Multiples.lean` proves G's order n: the kernel
computes (n - 1)·G by doubling and adding, checking each step's coordinates
against the group law, and finds -G, and `Rind/N256Prime.lean` proves n
prime. So a scalar in [1, n) times G is a finite point. That the same holds
for the peer's point, so the fault never happens, needs every point's order,
which follows from the group having n points, a count these theorems do not
prove.

P-256 ECDSA with SHA-256 and fixed-length signatures on aarch64, from the
signature API's `EcdsaKeyPair` and `PublicKey` to s2n-bignum's routines, in
`Rind/Aarch64/P256Signature.lean` over `Rind/Aarch64/P256Ecdsa.lean`:

- `p256_ecdsa_generate`: the key pair's scalar is in [1, n), and generation
  is refused only if the system source's draws fail;
- `p256_ecdsa_from_scalar_and_public_key`: a scalar that is not 32 bytes
  is refused, so is one outside [1, n), and so is a public key that is neither
  X9.62 encoding, uncompressed or compressed, of the scalar times G, and
  otherwise the key pair's scalar is the scalar;
- `p256_ecdsa_sign`: a signature signing returns is 64 bytes, the big-endian
  r and s of the ECDSA signature of the message's SHA-256 under the scalar,
  for some nonce in [1, n), neither zero, and signing is refused only if the
  nonce's random input cannot be drawn;
- `p256_ecdsa_key_pair_public_key`: the public key's bytes are the X9.62
  uncompressed encoding of the scalar times G;
- `p256_ecdsa_public_key_new`: a public key is refused unless it is a 65-byte
  uncompressed point whose coordinates are below p and on the curve, and
  otherwise its `verify` accepts exactly the signatures ECDSA verifies with
  that point: 64 bytes, r and s in [1, n), and the x-coordinate of
  e/s·G + r/s·Q, a finite point, equal to r mod n;
- `p256_ecdsa_key_pair_verify`: a key pair's public key verifies the same
  way, with its point the scalar times G.

`ecdsaP256Sign` and `ecdsaP256Verifies` in `Rind/Spec.lean` are FIPS 186-5's,
over `p256Pow` and `p256Add`. `Rind/P256Multiples.lean` proves, from
`Rind/P256Group.lean`'s group, the laws by which the twin multiplication's
windowed sum is e/s·G + r/s·Q, and `Rind/N256Prime.lean` that n is prime, so
every nonzero scalar has an inverse. The sum also needs Q's order n. A key
pair's Q is its scalar times G, whose order follows from G's, but a parsed
public key's is any point on the curve, so `p256_ecdsa_public_key_new` takes
`P256Order`: every finite point on the curve has order n, as HOL Light's
`P256_GROUP_ELEMENT_ORDER` proves from the group's size, which Mathlib cannot
count yet. Key generation and signing need only G's order. The message's
SHA-256 is FIPS 180-4's (`sha256E`), through the SHA-256 proof below, so
signing and verification take its `Sha256Blocks` and messages of at most
`maxInput` bytes. Signing draws nonces until r and s are both
nonzero, with no bound, so `p256_ecdsa_sign` says what a returned signature
is, not that one returns. The nonces come from RFC 6979's HMAC-DRBG, hedged
with 16 bytes from the system source; its update takes a slice of borrowed
slices, which Aeneas cannot translate, so it is opaque, and the theorems
assume `Drbg`: it seeds and draws without panicking, and a draw never fails.
They also assume `Fills`, that the system source returns, `Held`, that the
entry guard holds, and `Cached`: a verifying key's lock-free caches of P to
15P and 17P to 31P, and a signing key's of its encoded public key, whose
atomics Aeneas cannot translate, are built from the key's own point or
scalar.

P-384 ECDH's agreement on x86_64 and aarch64, from the same `PrivateKey` to
s2n-bignum's routines, in `Rind/X86_64/P384.lean`, which `admin/prove` also
writes for aarch64:

- `p384_agree`: a peer key is refused unless it is a 97-byte uncompressed
  point whose coordinates are below p and on the curve, and otherwise the
  secret is the 48 big-endian bytes of the x-coordinate of the scalar times
  that point, or a fault unless that is a finite point on the curve;
- `p384_shared_secret`: the secret's bytes are those.

Key generation, a loaded key, and the public key a key holds run rind's comb
for k·G, which no theorem covers yet. `p384Pow` is HOL Light's `group_pow
p384_group`, whose group law `Rind/Nist.lean` defines once for the NIST
curves, and `Rind/NistGroup.lean` proves it is multiplication in Mathlib's
group of points on such a curve. `Rind/P384Group.lean` proves p and n prime,
by Pratt certificates that `Rind/Pratt.lean` checks, and G's order n.

ChaCha20 QUIC header protection on x86_64 and aarch64, from
`HeaderProtectionKey` to HACL*'s rounds, in `Rind/X86_64/ChaCha20.lean`:

- `chacha20_new`: a key that is not 32 bytes is refused, and otherwise the
  key holds its bytes;
- `chacha20_mask`: the mask is RFC 9001's, the first five bytes of RFC 8439's
  keystream block for the key, with the sample's first four bytes as the
  little-endian block counter and the rest as the nonce.

HACL*'s rounds are Rust, so they are translated and proven with the rest, and
no axiom stands in for HACL*'s proof of them.

Theorems that run an entry guard assume `Runs`: rind's CPU-feature checks
pass, which no input affects. `Rind/Aarch64/P256Table.lean` proves that
rind's generator table holds the multiples of G that s2n-bignum's proof of
`p256_scalarmulbase` assumes, so `p256_public_key` assumes nothing of it.
`Rind/<Arch>/Axioms.lean` checks the axioms each theorem rests on.

SHA-1 and SHA-256's padding and finalization, and HMAC's keyed states over
any hash, on x86_64 and aarch64, in `Rind/X86_64/{Blockwise,Sha,Hmac}.lean`,
against FIPS 180-4 and RFC 2104 as `Rind/HashSpec.lean` transliterates them:

- `sha256_hash`, `sha1_hash`: a message's digest, one-shot, and
  `sha256_hashSpec`, `sha1_hashSpec`: every method of each `Hash` impl,
  streaming included;
- `hmac_key_new_spec`, `hmac_sign_spec`, `hmac_start_spec`,
  `hmac_update_spec`, `hmac_finish_spec`: `HmacKey` and `Hmac` over any hash
  meeting `HashSpec`, and `hmac_sha256_sign`, `hmac_sha1_sign` over SHA-256
  and SHA-1.

Below rind's padding, these theorems take `Sha1Blocks` or `Sha256Blocks` as
a hypothesis, in each target's own `Rind/<Arch>/ShaBlocks.lean`. No proof
covers a SHA-1 block function rind runs, or a SHA-256 one on x86_64, so there
each states that every routine computes FIPS 180-4's block function, x86_64's
SHA extensions' routines for SHA-1's padded last blocks and SHA-256's finish
pad, and SHA-256's encodes, as FIPS 180-4 does, and that rind's checks pass.
On aarch64, `Sha256Blocks` states only that the CPU has the crypto extension
and rind's checks pass: `Rind/Aarch64/Sha256Hw.lean` restates the HOL Light
proof above as the axiom `sha256_block_data_order_hw_spec`, and
`Rind/S2nSha256.lean` proves s2n-bignum's spec FIPS 180-4's block function.
`Rind/<Arch>/HashAxioms.lean` checks the axioms each theorem rests on: none
on x86_64, and that one for SHA-256 on aarch64. An input is at most `maxInput`
(2^61 - 1) bytes, under FIPS 180-4's 2^64-bit limit. `Rind/HashSpecTest.lean`
checks the transliterations against FIPS 180-4's, RFC 4231's, RFC 5869's, and
RFC 6070's vectors.

The APIs above them, on x86_64 and aarch64, over SHA-1 and SHA-256 and, where
they take an HMAC algorithm, SHA-384 and SHA-512, against RFC 2104, RFC 5869,
and RFC 8018 as `Rind/HashSpec.lean` transliterates them:

- `digest_spec`, `digest_ctx_new_spec`, `digest_ctx_update_spec`,
  `digest_ctx_finish_spec` (`Rind/X86_64/DigestApi.lean`): `digest::digest`
  and `digest::Context` over SHA-1 and SHA-256;
- `key_new_spec`, `sign_spec`, `verify_spec`, `context_with_key_spec`,
  `context_update_spec'`, `context_sign_spec` (`Rind/X86_64/HmacApi.lean`):
  `hmac::Key`, `sign`, `verify`, and `Context`;
- `kdf.salt_extract_spec`, `kdf.okm_fill_spec`, `kdf.hkdf_fill`
  (`Rind/X86_64/Hkdf.lean`): HKDF's extract and expand;
- `kdf.derive_spec`, `kdf.verify_spec` (`Rind/X86_64/Pbkdf2.lean`): PBKDF2's
  `Secret::derive` and `Secret::verify`.

HKDF's `From<Okm>` conversions, each filling the key's length of HKDF-Expand
into a zeroed buffer and keying it, in `Rind/X86_64/Hkdf.lean` on both targets
and `Rind/X86_64/HkdfAead.lean` on x86_64:

- `hmac_key_from_spec`, `prk_from_spec`: the `hmac::Key` and `Prk` are keyed
  under the algorithm with the `tag_len` bytes of HKDF-Expand;
- `header_key_from_spec`: ChaCha20 header protection holds the 32 bytes of
  HKDF-Expand, through `header_new_spec` over `chacha20_new`;
- `aead_key_from_spec`: an AES-128-GCM or AES-256-GCM key holds AES-GCM on
  Vale's tier for the `4 * nk` bytes of HKDF-Expand, under `RunsValeAesGcm`,
  through `aead_key_new_spec` over `aes_gcm_new`;
- `aead_key_from_chacha20_poly1305_spec`: a ChaCha20-Poly1305 key holds the
  32 bytes of HKDF-Expand, through `aead_key_new_chacha20_poly1305_spec` over
  `chacha20_poly1305_new`;
- `aes_header_key_from_spec`: AES-128 or AES-256 header protection holds
  FIPS 197's round keys for the `4 * nk` bytes of HKDF-Expand, on x86_64 under
  `RunsAesNi`, through `aes_header_new_spec` over `aes_header_new`.

The other keys `From<Okm>` converts to, AES-192-GCM and AES header protection
on aarch64, have no proof. `Rind/X86_64/Kdf/FunsExternal.lean`'s
`new` wrappers turn a model's refusal into the panic its `expect` makes, so
each conversion panics exactly where its `expect` does.

`hmac::Key` and `Context` reach each hash through function pointers, which
`Rind/X86_64/HmacDispatch.lean` models. HKDF and PBKDF2 call that model, so
`admin/prove` translates `high::hkdf` and `high::pbkdf2` in a second pass,
into `Rind/<Arch>/Kdf/{Types,Funs}.lean`, with the first pass's items and the
HMAC model opaque below it; `Rind/X86_64/HkdfExpand.lean` models
`Prk::expand_into`, whose slice of borrowed slices Aeneas cannot translate.
The theorems over an HMAC algorithm assume `RunsHmac`: `Sha1Blocks` for SHA-1,
`Sha256Blocks` for SHA-256, and `RunsSha512` for SHA-384 and SHA-512, so `Rind/<Arch>/Axioms.lean`
checks their axioms.
`hmac::verify` and `Secret::verify` compare through `low::generic::ct_equal`,
which `Rind/X86_64/CtEqual.lean` proves returns whether its inputs are equal,
from axioms restating the HOL Light proofs of the `asm!` compares below it.

`PrivateKey` reaches each curve's `Agree` impl through function pointers
(`Algorithm`'s `generate` and `load`, and `Keyed`'s `Ops`), and `HeaderProtectionKey` each
cipher's `Mask` impl (`Algorithm`'s `new` and `Masker`'s `mask`), which Aeneas
cannot translate. `Rind/X86_64/Dispatch.lean` models that dispatch by hand, in
Lean definitions beside the Rust they model, with an agreement `Algorithm` as
which static it is. P-256's key generation draws through a `dyn
RandomSource`, which Aeneas cannot translate either, and
`Rind/Aarch64/P256Dispatch.lean` models it the same way, for
`Rind/Aarch64/Dispatch.lean` to call; on x86_64, where no theorem is about
P-256, `Rind/X86_64/P256Dispatch.lean` leaves it opaque. The signature API's `EcdsaKeyPair` reaches each curve's code, and
`PublicKey` each ECDSA key's parser and verifier, through function pointers,
and P-256's ECDSA key generation draws through a `dyn RandomSource`;
`Rind/Aarch64/EcdsaDispatch.lean` models them for P-256 with SHA-256 and
fixed-length signatures.

SHA-384, SHA-512, and SHA-512/256, from the digest API to aws-lc's block
routine, in `Rind/X86_64/Sha512.lean`, which `admin/prove` also writes for
aarch64:

- `sha512_family_digest`: `digest`'s bytes are the hash of the message;
- `sha512_family_context`: a `Context` given the message in any chunks, then
  finished, returns its hash, for messages under 2^64 bytes.

The hash is cryptol-specs' FIPS 180-4 SHA-512, in `Rind/Sha2.lean`, with its
block compression `processBlock_Common` opaque. Each theorem assumes
`RunsSha512`: on x86_64 that rind picks aws-lc's AVX routine, on an Intel CPU
with AVX but without AVX2, and on aarch64 its scalar routine, on a CPU without the SHA-512
instructions; those are the routines whose proofs state their result. The
digest API reaches each hash through function pointers too, which
`Rind/X86_64/DigestDispatch.lean` models, and `Rind/X86_64/DigestAlgorithm.lean`
models the `Algorithm` statics that hold them, and `Digest`, whose
`&'static Algorithm` Aeneas cannot end a borrow of `Digest` across.

SHA3-256, SHA3-384, and SHA3-512, and the SHAKE calls ML-KEM makes, on x86_64
and aarch64, from rind's Rust sponge to s2n-bignum's Keccak-f routines, in
`Rind/X86_64/Sha3.lean`, which `admin/prove` also writes for aarch64:

- `sha3_family_digest`: `digest`'s bytes are the hash of the message;
- `sha3_family_context`: a `Context` given the message in any chunks, then
  finished, returns its hash;
- `sha3Family_fips202`: those hashes are FIPS 202's SHA3-256, SHA3-384, and
  SHA3-512;
- `sponge_absorb_spec`, `sponge_finish_spec`, `squeezing_squeeze_spec`: a
  `Sponge` absorbs any message in any pieces, and once finished, each
  `squeeze` writes the next bytes of FIPS 202's sponge on it, as ML-KEM's J
  (SHAKE256) and its matrix sampling's tail draw;
- `shake128x4_new_spec`, `shake128x4_squeeze_spec`: `SqueezingSponge4xShake128`
  writes the first 504 bytes of SHAKE128 on each of four 34-byte inputs, and
  returns the sponges to squeeze the rest;
- `shake256_batch_spec`: `shake256_batch` writes the first 128 bytes of
  SHAKE256 on each of its 33-byte inputs, four at a time.

The sponge is `Rind/Sha3.lean`'s, over bytes, which `sha3_256_eq` and its
siblings, `shake128_eq` and `shake256_eq`, prove FIPS 202's as SymCrypt's
Lean spec (`Rind/SymCrypt/Sha3.lean`, MIT) states it. Keccak-f is
s2n-bignum's `keccak 24` on lanes, the spec its routines' theorems state,
which `Rind/Keccak.lean` proves SymCrypt's KECCAK-f[1600].
`Rind/<Arch>/KeccakDispatch.lean` proves what rind's dispatch to the one-,
two-, and four-state routines computes, from those theorems. Each theorem
assumes `RunsSha3`: rind's entry guard and CPU checks pass. ML-DSA's SHAKE
readers are not translated, and x86_64's AVX-512 eight-way Keccak, which
ML-KEM's sampler runs, has [its own quest](/quest/m4/verified/mlkem-avx512-sampler.md).

Ed25519 on x86_64 and aarch64, from the signature API's `Ed25519KeyPair` and
`PublicKey` to s2n-bignum's routines and the SHA-512 proof above, in
`Rind/X86_64/Ed25519.lean`, which `admin/prove` also writes for aarch64:

- `ed25519_generate`: the key pair's seed is the 32 drawn bytes, and a failed
  draw is refused;
- `ed25519_from_seed_and_public_key`: a seed that is not 32 bytes is refused,
  so is a public key that is not the seed's, and otherwise the key pair's
  seed is the seed;
- `ed25519_sign`: the signature's bytes are RFC 8032's PureEd25519 signature
  of the message under the seed;
- `ed25519_key_pair_public_key`: the public key's bytes are RFC 8032's public
  key of the seed;
- `ed25519_public_key_new`: a public key is refused unless it is 32 bytes,
  refused if its low 255 bits are one of libsodium's seven small-order
  y-coordinates, refused unless it encodes a point of the group, and
  otherwise its `verify` accepts exactly the signatures RFC 8032 verifies with
  that point: 64 bytes, S below L, and R the encoding of SB - kA;
- `ed25519_key_pair_verify`: a key pair's public key verifies the same way,
  with its point the base point times its secret scalar, for a scalar whose
  multiple is a point of the group.

The spec, in `Rind/Ed25519.lean`, is RFC 8032 over HOL Light's
`edwards25519_group`, whose multiplication and power stay opaque, with
s2n-bignum's `ed25519_encode` and `ed25519_decode` of its points. Each theorem
assumes `Runs` and `RunsSha512`, and each with a message bounds it at
2^64 - 64 bytes. The two that verify also assume `RunsDouble`: on x86_64
that a CPU without ADX lacks AVX2 too, since with it rind runs a port of
curve25519-dalek's AVX2 backend, which nothing proves, and on aarch64
nothing. That a multiple of the base point is a point of the group,
which `ed25519_key_pair_verify` assumes, is the group's theory, which these
theorems do not import. `PublicKey` reaches each algorithm's key parser, and
each parsed key its verification, through function pointers, which
`Rind/X86_64/SignatureDispatch.lean` models.

AES-128 and AES-256 on x86_64 CPUs with AES-NI, from `cipher::Aes` and the
header-protection API's `HeaderProtectionKey` to rind's AES-NI key expansion
and block cipher, in `Rind/X86_64/AesCipher.lean`:

- `aes_new`: a `cipher::Aes` key that is not the algorithm's length is
  refused, and otherwise the key holds FIPS 197's round keys for its bytes,
  as Vale's `key_to_round_keys_LE` lays them out;
- `aes_encrypt_block`: the block becomes Vale's `aes_encrypt_LE` of it under
  the key;
- `aes_header_new`: the same for `aead::quic::AES_128` and `AES_256`, whose
  keys reach `Aes::new` through the dispatch `Rind/X86_64/Dispatch.lean`
  models;
- `aes_header_mask`: the mask is RFC 9001's, the first five bytes of that
  cipher of the sample.

`aesBlock` and `aesHeaderMask` are those specs on bytes, which `#guard`s
check against FIPS 197's and RFC 9001's vectors. The theorems assume
`RunsAesNi`, or for a key already made only its entry guard: rind's
CPU-feature checks find AES-NI, which no input affects. AES-192 keys, which
run `aes192_expand` and `aes_block`, and aarch64, whose intrinsics nothing
models yet, have no proof: [the AES header-protection
quest](/quest/m4/verified/aes-header-protection.md) owns them.

AES-128-GCM and AES-256-GCM on x86_64 CPUs with AVX and MOVBE but no VAES,
from the AEAD API's `Key` to HACL*'s Vale AES-GCM routines, in
`Rind/X86_64/AesGcm.lean`:

- `aes_gcm_new`: a key that is not the algorithm's length is refused, and
  otherwise the key holds FIPS 197's round keys for its bytes, as Vale's
  `key_to_round_keys_LE` lays them out, and the GHASH key powers Vale's
  `hkeys_reqs_pub` requires of `E_K(0)`;
- `aes_gcm_seal`: for AAD under 2^32 bytes and messages of 129 bytes up to
  that, the ciphertext in place and the tag are Vale's `gcm_encrypt_LE` of the
  key, nonce, message, and AAD;
- `aes_gcm_seal_append_tag`: the same for a seal that appends the tag to any
  buffer: the ciphertext lands in the view its `as_mut` gives, and the call
  returns what its `extend` makes of that, handed the tag; and
  `aes_gcm_seal_append_tag_vec`: a `Vec<u8>` with room for the tag becomes
  the ciphertext followed by the tag, assuming `VecAsMut` and `VecExtend`,
  that std's impls view the whole vector and append the tag as
  `extend_from_slice` does;
- `aes_gcm_open_separate_tag` and `aes_gcm_open`: for AAD and messages under
  2^32 bytes, the call succeeds exactly when Vale's `gcm_decrypt_LE` accepts
  the tag, leaving its plaintext in place, and otherwise fails, leaving zeros.

Longer AAD or messages run the by-8 code, which no proof covers, as do
seals of messages under 129 bytes, where it is faster, and AES-192 keys, for
which Vale has no routine. The key setup is rind's: its AES-NI key expansion and block cipher, and its
PCLMULQDQ GHASH key powers, whose Karatsuba product and reduction
`Rind/Gf128.lean` proves to be Vale's `gf128_mul_rev` of the shifted keys
(`mul_shiftKey1`). The rest is the Rust around Vale's routines, which
zero-pads the partial blocks and picks the six-block loop's share, as
EverCrypt's proven Low* wrapper does. It pads them with GHASH's
`load_partial` and `store_partial`, whose overlapping loads and stores
`Rind/X86_64/PartialBlock.lean` proves are the bytes at every length. The theorems assume `RunsValeAesGcm`: rind's CPU-feature
checks pick Vale's tier. `Rind/X86_64/AeadDispatch.lean` models the AEAD API's
function pointers (`Algorithm`'s `expand` and `Sealer`'s `Ops`), and
`seal_in_place_append_tag`, which is generic over its buffer.

`aead::gcm::Key`, which takes an IV of any length, is proven on the same
tier for a 12-byte IV and full 16-byte tags, in `Rind/X86_64/GcmKey.lean`, a
hand model over `AeadDispatch` that quotes `rind/src/aead/gcm.rs`. Its
`new` for AES-128 or AES-256 holds the `aead::Key` for the algorithm, which
refuses a key of another length, and its `seal_in_place_separate_tag`,
`seal_in_place_append_tag`, `open_in_place`, and `open_in_place_separate_tag`
are `aead::Key`'s: `gcm_key_new`, `gcm_key_seal`, `gcm_key_seal_append_tag`,
`gcm_key_open`, and `gcm_key_open_separate_tag`. The seals take messages of 129
bytes and more, as `aes_gcm_seal` does, and every theorem bounds AAD and
messages under 2^32 bytes. The other IV lengths and truncated tags run
`encrypt_any` and `decrypt_any`, which no proof covers; the model leaves those
arms opaque, and [the by-8 intrinsics quest](/quest/m4/verified/aes-gcm-x86-intrinsics.md)
owns them.

ChaCha20-Poly1305 and XChaCha20-Poly1305 on x86_64 CPUs with SSE4.1, from
the AEAD API's `Key` and `RandomizedNonceKey` down to the call of aws-lc's
one-pass routines, in `Rind/X86_64/ChaCha20Poly1305.lean`:

- `chacha20_poly1305_new`: a key that is not 32 bytes is refused, and
  otherwise the key holds its bytes;
- `chacha20_poly1305_seal`, `chacha20_poly1305_seal_append_tag`, and
  `chacha20_poly1305_seal_append_tag_vec`: a message past 2^38 - 64 bytes, as
  many as the 32-bit block counter covers from block 1, is refused and left as
  it is, and otherwise the ciphertext and the tag are RFC 8439 section 2.8's;
- `chacha20_poly1305_open_separate_tag` and `chacha20_poly1305_open`: past
  2^38 - 64 bytes the same refusal, and otherwise the call succeeds exactly
  when RFC 8439's tag is the one given, leaving the plaintext in place, and
  otherwise fails, leaving zeros;
- `randomized_nonce_key_new`, `randomized_nonce_key_seal_append_tag_vec`,
  and `randomized_nonce_key_open`: the same for draft-irtf-cfrg-xchacha-03's
  XChaCha20-Poly1305, under the nonce the system's random source fills, whose
  failure the seal returns as `RngFailed`.

HChaCha20, which derives XChaCha20's subkey, runs HACL*'s rounds, which
`hchacha20_spec` proves. The theorems assume `RunsChaCha20Poly1305`: rind's
CPU-feature checks find SSE4.1, and `OnePass`, that aws-lc's one-pass
routines compute RFC 8439's AEAD, which no proof covers yet;
[the ChaCha20-Poly1305 quest](/quest/m4/verified/chacha20-poly1305-x86/aead.md)
owns their HOL Light proofs. CPUs without SSE4.1 run the separate ChaCha20
and Poly1305 passes, which the model leaves opaque. `AeadDispatch` models
`RandomizedNonceKey`, which reaches the system's random source, and
`Rind/ChaCha20Poly1305Test.lean` checks `Rind/Spec.lean`'s transliterations
against RFC 8439's and draft-irtf-cfrg-xchacha-03's test vectors.

`admin/prove` fails if a hand model's quote no longer matches the source, if
the source names `Ops`, builds a `Masker`, or writes its `mask` outside the
dispatch models' quotes, if it builds a digest `Algorithm` outside
`DigestAlgorithm.lean`'s, if it mentions `Verification::Ed25519(` or
`Parsed::Ed25519(` outside `SignatureDispatch.lean`'s, or if it mentions
`Verification::Ecdsa(`, `EcdsaP256`, or `EcdsaKey::`, builds an `EcdsaOps` or
`EcdsaPair`, or reads an `ops` outside the signature models' quotes.

## Layout

- `hol-light/<arch>/`: rind's HOL Light proofs, one file per routine, and
  `hol-light/s2n-bignum/`, what they add to s2n-bignum: unmerged specs and
  rind's additions to the x86 model, with its cosimulation.
- `Rind/<Arch>/{Types,Funs}.lean`: Aeneas's translation, which `admin/prove`
  writes and git ignores.
- `Rind/<Arch>/{Types,Funs}External.lean` and `Rind/Core.lean`: what the
  translation leaves opaque, and models of the few `core` items Aeneas's
  library lacks.
- `Rind/<Arch>/S2nBignum.lean`, `Rind/<Arch>/AwsLc.lean`, and
  `Rind/X86_64/ValeAesGcm.lean`: s2n-bignum's, aws-lc-verification's, and
  Vale's theorems, restated as axioms about the routines' Rust wrappers.
- `Rind/X86_64/Simd.lean` and `Rind/X86_64/AesNi.lean`: models of the x86_64
  intrinsics rind's AES-GCM setup and partial blocks call, and of its AES-NI
  key expansion and block cipher, which load and store through raw pointers.
- `Rind/Spec.lean` and `Rind/Bytes.lean`: the elliptic-curve, ChaCha20,
  Poly1305, and ChaCha20-Poly1305 specs and byte-conversion lemmas, and
  `Rind/ChaCha20Poly1305Test.lean`, the AEAD specs' known-answer tests; `Rind/Sha2.lean` and
  `Rind/Sha2Lemmas.lean`: SHA-512's; `Rind/Ed25519.lean`: Ed25519's;
  `Rind/HashSpec.lean`: SHA-1's, SHA-256's, HMAC's, HKDF's, and PBKDF2's, and
  `Rind/HashSpecTest.lean`, their known-answer tests; `Rind/Vale.lean`,
  `Rind/ValeBytes.lean`, and `Rind/Gf128.lean`: Vale's AES and GF(2^128) specs
  and their lemmas.
- `Rind/X86_64/{Dispatch,DigestDispatch,DigestAlgorithm,SignatureDispatch,AeadDispatch,HmacDispatch,GcmKey}.lean`:
  the hand models of the agreement, header-protection, digest, signature,
  AEAD, and HMAC APIs' dispatch, and of `aead::gcm::Key` over the AEAD model; `Rind/X86_64/HkdfExpand.lean` and
  `Rind/X86_64/Kdf/{TypesExternal,FunsExternal}.lean`, of what the HKDF and
  PBKDF2 pass leaves opaque.
- `Rind/X86_64/{X25519,Sha512,ChaCha20,Ed25519}.lean`: the X25519, SHA-512,
  ChaCha20, and Ed25519 proofs, `Rind/X86_64/{Blockwise,Sha,Hmac}.lean`,
  SHA-1's, SHA-256's, and HMAC's, and
  `Rind/X86_64/{DigestApi,HmacApi,Hkdf,Pbkdf2}.lean`, the digest, HMAC, HKDF,
  and PBKDF2 APIs'; `Rind/X86_64/HkdfAead.lean`, HKDF's conversion to AES-GCM,
  ChaCha20-Poly1305, and AES header-protection keys;
  `Rind/X86_64/AesCipher.lean`, `cipher::Aes` and AES header protection, and
  `Rind/X86_64/{AesKey,Ghash,PartialBlock,AesGcmGlue,AesGcm}.lean`:
  the AES-GCM proof, on x86_64 alone; `Rind/X86_64/GcmKey.lean`, the hand model
  of `aead::gcm::Key` and its proofs; `Rind/X86_64/ChaCha20Poly1305.lean`, the
  ChaCha20-Poly1305 and XChaCha20-Poly1305 proof above aws-lc's routines.
- `Rind/SymCrypt/{Defs,Sha3}.lean`: SymCrypt's Lean FIPS 202 spec, vendored;
  `Rind/Keccak.lean`: s2n-bignum's Keccak spec, transliterated, and its proof
  that it is SymCrypt's; `Rind/Sha3.lean`: the sponge over bytes, and its
  proof that it is SymCrypt's; `Rind/<Arch>/KeccakDispatch.lean`: rind's
  Keccak-f dispatch on each target; `Rind/X86_64/Sha3.lean`: the SHA-3 and
  SHAKE proofs.
- `Rind/<Arch>/ShaBlocks.lean`: SHA-1 and SHA-256's block functions on each
  target, SHA-1's padded last blocks, and SHA-256's padded last blocks and
  finish; `Rind/Aarch64/Sha256Hw.lean`, the axiom for aarch64's routine with
  the SHA-256 instructions, and `Rind/S2nSha256.lean`, s2n-bignum's SHA-256
  spec, transliterated, and its proof that it is `Rind/HashSpec.lean`'s.
- `admin/prove` copies the other `Rind/X86_64/` models and proofs to
  `Rind/Aarch64/` with the target renamed.
- `Rind/P256Group.lean`: that `p256` is prime, by a Pratt certificate, and
  that `p256Add` is the addition of Mathlib's group of points on the curve;
  `Rind/N256Prime.lean`: that `n256` is prime; `Rind/P256Multiples.lean`: the
  group laws and multiples ECDSA's twin multiplication relies on.
- `Rind/Aarch64/P256Dispatch.lean`, `Rind/Aarch64/P256Table.lean`, and
  `Rind/Aarch64/P256.lean`: the hand model of P-256's key generation, the
  generator table's proof, and the P-256 ECDH proof.
- `Rind/Aarch64/EcdsaDispatch.lean`, `Rind/Aarch64/P256Ecdsa.lean`, and
  `Rind/Aarch64/P256Signature.lean`: the hand model of ECDSA's dispatch and
  key generation, the proof of `high::ecdsa` and `mid::p256`'s ECDSA at
  P-256, and the signature API's theorems.

## Trust base

Beyond Lean's kernel:

- Charon and Aeneas's translation, and Aeneas's models of `core`, with
  `Rind/Core.lean`'s.
- That each hand model computes what the Rust it quotes does. They add no
  axiom.
- That `Rind/HashSpec.lean` transliterates FIPS 180-4, RFC 2104, RFC 5869,
  and RFC 8018.
- The restatement of each s2n-bignum and aws-lc-verification theorem as an
  axiom, under the composition rule in the
  [verification epic](/quest/m3/verified/README.md), and on aarch64 the
  caveats aws-lc-verification lists for its NSym proof. It lets a
  group-membership fact a proof must decide be its defining equation, so
  `group_carrier p256_group` is the curve equation that HOL Light's
  [`P256_GROUP`](https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp256.ml#L82)
  proves it is, and `group_carrier edwards25519_group` the one
  [`EDWARDS25519_GROUP`](https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/edwards25519.ml#L92)
  does. A function a proof must compute, such as `group_pow p256_group`, is
  its HOL Light definition, transliterated, rather than opaque, so `p256Add`,
  `p256Pow`, and `p256Inv` in `Rind/Spec.lean` are trusted to be
  `weierstrass_add`, `group_pow`, and `ring_inv` on `p256_group`.
- That `Rind/SymCrypt/Sha3.lean` is FIPS 202, as SymCrypt's authors state,
  and that `Rind/Keccak.lean` transliterates s2n-bignum's `keccak_spec.ml`,
  in which the Keccak-f axioms state their results.
- That `Rind/Sha2.lean` restates cryptol-specs' SHA-512 around
  `processBlock_Common`, and `Rind/S2nSha256.lean` transliterates
  s2n-bignum's SHA-256 spec.
- That `Rind/Spec.lean`'s ChaCha20, Poly1305, and ChaCha20-Poly1305
  transliterate RFC 8439 and RFC 9001, its HChaCha20 and XChaCha20-Poly1305
  draft-irtf-cfrg-xchacha-03, its ECDSA FIPS 186-5, and
  `Rind/Ed25519.lean` RFC 8032 and s2n-bignum's encoding and decoding of
  edwards25519 points, whose `ed25519_decode` picks by Hilbert's choice as
  Lean's `Classical.epsilon` does.
- That `Rind/Vale.lean` transliterates Vale's AES and GF(2^128) specs and
  `hkeys_reqs_pub`, with the round functions Vale's AES spec assumes read as
  FIPS 197's, the S-box and `MixColumns` opaque.
- That `Rind/X86_64/Simd.lean`'s intrinsics compute what their instructions
  do beyond the inputs `admin/prove` tests them on. `admin/simd-vectors.rs`
  runs each instruction on the checking machine's CPU, on every immediate it
  reads, zero and all-ones lanes, and random inputs from a fixed seed, and
  Lean checks each model gives the same. The AES models run the S-box and
  `MixColumns` as FIPS 197 computes them, bodies Lean evaluates while proofs
  keep the two opaque. All are tested on hardware, none under an emulator;
  `admin/prove` fails on a `core.core_arch` model it does not test.
- That rind's inline assembly is s2n-bignum's, aws-lc's, and Vale's object
  code, as for `benchmarks/verified.toml`'s other entries, except where a
  proof in `hol-light/` covers the bytes rind's build emits. For those, HOL
  Light's kernel and s2n-bignum's instruction models, as for s2n-bignum's
  own theorems, with rind's additions in `hol-light/s2n-bignum/x86.patch`,
  which `admin/prove cosim` checks against the CPU as s2n-bignum checks its
  own.
- The translation ignores drops, which here wipe keys and keyed state under
  the `wipe` feature and restore CPU state, and computes nothing an output
  depends on.
