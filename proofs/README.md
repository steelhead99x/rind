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

`lakefile.toml` turns on Lake's artifact cache, which lives in the Lean
toolchain's directory under `~/.elan` and every checkout of a user shares, so
a new worktree hard-links, or across filesystems copies, the Mathlib and
Aeneas builds and the unchanged modules another checkout already fetched or
built rather than unpacking or building its own. The cache outlives the
worktrees: uninstalling the old toolchain after a bump with `elan toolchain
uninstall` drops it, and `lake cache clean` in `proofs/` empties it at any
time, since each checkout keeps its own links and its next build puts them
back.

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

To develop one, `nix develop .#hol-light --command admin/prove session
<arch> [<file>]` starts a HOL Light session, on Linux, in which a proof
loads as `admin/prove hol-light` compiles it: s2n-bignum's `base.ml` for
`x86_64` or `aarch64` loaded, on the same load path, in the directory
holding the object code the proofs read. Given a file, such as
`proofs/hol-light/x86_64/ct_compare_16.ml`, it loads it and exits, failing if
any of it fails; otherwise it reads OCaml from stdin. Loading `base.ml`
takes minutes, so the first session on a set of inputs (HOL Light, DMTCP,
the submodule's commit, and what `hol-light/s2n-bignum/` carries)
checkpoints it with DMTCP into an image of about 400 MB in
`~/.cache/rind/hol-light/`, which every later session on those inputs, in
any worktree, restores in under a second. Like `admin/prove`, a session
first checks the submodule out at the commit rind pins, and it refuses one
with uncommitted changes, which that commit does not name.

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
- `aarch64/sha512_block_data_order_hw.ml`: `SHA512_HW_SUBROUTINE_CORRECT`,
  rind's proof that the naked function
  `low::aarch64::sha512::sha512_block_data_order_hw`, aws-lc's routine for
  the SHA-512 instructions, computes s2n-bignum's FIPS 180-4 spec,
  `sha512_hash_blocks`, and stores it to the state, as `sha256`'s above; the
  proof checks its round constants against FIPS 180-4's.
- `aarch64/bn_mul_mont.ml`: `BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT`, rind's
  proof that the naked function `low::aarch64::mont::bn_mul_mont`, aws-lc's
  Montgomery multiplication, writes the Montgomery product
  `x * y / 2^(64k) mod m` of its `k`-word operands, as s2n-bignum's
  `bignum_montmul` states it, given `-m^-1 mod 2^64` and
  `x * y <= 2^(64k) * m`, for every width from two up that is not a multiple
  of four: those its width-generic path runs, for `k < 2^58`, a 16-aligned
  stack pointer, and `z` and the stack frame disjoint from the code and the
  inputs, so `z` may not alias `x`. The theorem covers the dispatch,
  the stack frame of up to `8k + 72` bytes below the stack pointer, and the
  callee-saved registers it restores. The widths that run `__bn_mul4x_mont`
  and `__bn_sqr8x_mont`, which include every standard RSA size and its CRT
  primes, are not proven yet, and no axiom in `Rind/` restates the theorem
  yet. The function has no relocations.
- `x86_64/bn_mul_mont_nohw.ml`: `BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT`, rind's
  proof that the naked function `low::x86_64::mont::bn_mul_mont_nohw`,
  aws-lc's word-serial Montgomery multiplication, writes the Montgomery
  product `x * y / 2^(64k) mod m` of its `k`-word operands, from two words up,
  as s2n-bignum's `bignum_montmul` states it, given `-m^-1 mod 2^64` and
  `x * y <= 2^(64k) * m`. The theorem covers the whole function: its stack
  frame of up to `8k + 1088` bytes below the stack pointer, aligned and probed
  a page at a time, and the callee-saved registers it restores. The function
  has no relocations, so its object is its section alone.
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
not yet merged, rind's own RFC 8439 spec of ChaCha20, Poly1305, and
ChaCha20-Poly1305, `common/chacha20poly1305.ml`, whose known-answer tests
`admin/prove hol-light` runs, and `x86.patch`, rind's additions to the x86
model, which `x86-cosim.ml` checks against the CPU. Its
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

P-256 ECDH, from the same `PrivateKey` to s2n-bignum's routines, in
`Rind/Aarch64/P256.lean` on aarch64, and, for its agreement alone, in
`Rind/X86_64/P256Agree.lean`, which `admin/prove` also writes for aarch64, so
`p256_agree` and `p256_shared_secret` hold on x86_64 too, where key generation
runs aws-lc's generator multiplication, which no proof covers yet:

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

`p256Pow` is HOL Light's `group_pow p256_group`, defined as HOL Light does
once for the NIST curves in `Rind/Spec.lean`, and `Rind/NistGroup.lean`
proves it is multiplication in Mathlib's group of points on such a curve. `Rind/P256Multiples.lean` proves G's order n: the kernel
computes (n - 1)·G by doubling and adding, checking each step's coordinates
against the group law, and finds -G, and `Rind/N256Prime.lean` proves n
prime. So a scalar in [1, n) times G is a finite point. `p256_order` gives
every finite point order n too, by `Rind/NistOrder.lean`'s count of the
curve's points, but `p256_agree` does not yet use it to rule out its fault
case for the peer's point.

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
`Rind/NistGroup.lean`'s group, the laws by which the twin multiplication's
windowed sum is e/s·G + r/s·Q, and `Rind/N256Prime.lean` that n is prime, so
every nonzero scalar has an inverse. The sum also needs Q's order n. A key
pair's Q is its scalar times G, whose order follows from G's. A parsed public
key's is any point on the curve, whose order n is `p256_order`, HOL Light's
`P256_GROUP_ELEMENT_ORDER`: Mathlib has no Hasse bound to count the curve's
points, so `Rind/NistOrder.lean` counts them elementarily. Each x gives at
most two points, so the group has at most 2p + 1 < 3n; n divides its order,
as G has order n; and an order of 2n would give a point of order 2 by Cauchy,
whose x would be a root of x³ - 3x + b mod p, which the kernel checks has
none. So the order is n, a prime. The message's
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

P-384's key generation on x86_64 and aarch64, in `Rind/X86_64/P384Keygen.lean`,
which `admin/prove` also writes for aarch64, as P-256's is on aarch64:

- `p384_generate`: the key's scalar is the first of up to 64 draws from the
  system source whose bytes, read big-endian, are in [1, n), and generation is
  refused if a draw fails first or none is;
- `p384_from_scalar`: a scalar that is not 48 bytes is refused, so is one
  outside [1, n), and otherwise the key's scalar is the scalar;
- `p384_public_key`: a key's public key is the X9.62 uncompressed encoding of
  its scalar times G.

rind computes k·G with its own comb in Rust, aws-lc's layout: 77 Booth-recoded
5-bit windows added from 20 tables of 1 to 16 times 2^(20j)·G, with five
doublings between the four teeth. `Rind/P384Comb.lean` proves the windows'
digits sum to the scalar and that no mixed addition meets the equal points
s2n-bignum's `p384_montjmixadd` excludes, for a scalar below n, and
`Rind/X86_64/P384Table.lean` has the kernel check the translated tables
against G. The draws are modelled in `Rind/X86_64/P384Dispatch.lean`, as
P-256's are. The theorems take `AffSelect`, what the table lookup computes, as
a hypothesis: rind's AVX2, SSE2, and NEON selects load through raw pointers,
which Aeneas cannot translate, and are not modelled yet.

`p384Pow` is HOL Light's `group_pow p384_group`, whose group law
`Rind/Spec.lean` defines once for the NIST curves, and `Rind/NistGroup.lean`
proves it is multiplication in Mathlib's group of points on such a curve. `Rind/P384Group.lean` proves p and n prime,
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
into a zeroed buffer and keying it, in `Rind/X86_64/Hkdf.lean` and
`Rind/X86_64/HkdfAes.lean` on both targets and `Rind/X86_64/HkdfAead.lean` on
x86_64:

- `hmac_key_from_spec`, `prk_from_spec`: the `hmac::Key` and `Prk` are keyed
  under the algorithm with the `tag_len` bytes of HKDF-Expand;
- `header_key_from_spec`: ChaCha20 header protection holds the 32 bytes of
  HKDF-Expand, through `header_new_spec` over `chacha20_new`;
- `aead_key_from_spec`: an AES-128-GCM, AES-192-GCM, or AES-256-GCM key holds AES-GCM for
  the `4 * nk` bytes of HKDF-Expand, under `RunsAesGcm`, through
  `aead_key_new_spec` over `aes_gcm_new`;
- `aead_key_from_chacha20_poly1305_spec`: a ChaCha20-Poly1305 key holds the
  32 bytes of HKDF-Expand, through `aead_key_new_chacha20_poly1305_spec` over
  `chacha20_poly1305_new`;
- `aes_header_key_from_spec`: AES-128 or AES-256 header protection holds
  FIPS 197's round keys for the `4 * nk` bytes of HKDF-Expand, under
  `RunsAesHw`, through `aes_header_new_spec` over `aes_header_new`.

`Rind/X86_64/Kdf/FunsExternal.lean`'s `new` wrappers turn a model's refusal into the panic its `expect` makes, so
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
`Rind/X86_64/P256Dispatch.lean`, which `admin/prove` also writes for aarch64,
models it the same way, for `Rind/<Arch>/Dispatch.lean` to call. The signature API's `EcdsaKeyPair` reaches each curve's code, and
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
block compression `processBlock_Common` transliterated from FIPS 180-4 and
checked by `Rind/Sha2Test.lean` against its examples. Each theorem assumes
`RunsSha512`: on x86_64 that rind picks aws-lc's AVX routine, on an Intel CPU
with AVX but without AVX2, the routine whose proof states its result; on
aarch64 only that rind's checks pass, as both of aws-lc's routines there have
proofs: aws-lc-verification's of its scalar routine, and rind's HOL Light proof
above of its routine for the SHA-512 instructions, which
`Rind/Aarch64/AwsLc.lean` restates as the axiom
`sha512_block_data_order_hw_spec` and `Rind/S2nSha512.lean` proves
`Rind/Sha2.lean`'s. The
digest API reaches each hash through function pointers too, which
`Rind/X86_64/DigestDispatch.lean` models, and `Rind/X86_64/DigestAlgorithm.lean`
models the `Algorithm` statics that hold them, and `Digest`, whose
`&'static Algorithm` Aeneas cannot end a borrow of `Digest` across.

SHA3-256, SHA3-384, and SHA3-512, and the SHAKE calls ML-KEM and ML-DSA make, on x86_64
and aarch64, from rind's Rust sponge to s2n-bignum's Keccak-f routines, in
`Rind/X86_64/Sha3.lean`, which `admin/prove` also writes for aarch64:

- `sha3_family_digest`: `digest`'s bytes are the hash of the message;
- `sha3_family_context`: a `Context` given the message in any chunks, then
  finished, returns its hash;
- `sha3Family_fips202`: those hashes are FIPS 202's SHA3-256, SHA3-384, and
  SHA3-512;
- `sponge_absorb_spec`, `sponge_finish_spec`, `squeezing_squeeze_spec`: a
  `Sponge` absorbs any message in any pieces, and once finished, each
  `squeeze` writes FIPS 202's sponge on it from the next whole rate block,
  skipping what the last call left of its block, as ML-KEM's J (SHAKE256)
  and its matrix sampling's tail draw;
- `shake128x4_new_spec`, `shake128x4_squeeze_spec`: `SqueezingSponge4xShake128`
  writes the first 504 bytes of SHAKE128 on each of four 34-byte inputs, and
  returns the sponges to squeeze the rest;
- `shake256_batch_spec`: `shake256_batch` writes the first 128 bytes of
  SHAKE256 on each of its 33-byte inputs, four at a time;
- `shake_new_spec`, `shake_read_spec`: a `Shake` reader on a `Sponge` that
  has absorbed a message fills each `read`'s output with the next bytes of
  SHAKE on it, as ML-DSA's H (SHAKE256) and SampleInBall;
- `shake4x_new_spec`, `shake4x_squeeze_spec`: `Shake4x` absorbs one to four
  inputs shorter than a block, and each `squeeze` writes each lane's next
  whole blocks of SHAKE on its input, as ML-DSA's ExpandA (SHAKE128),
  ExpandS, and ExpandMask (SHAKE256).

The sponge is `Rind/Sha3.lean`'s, over bytes, which `sha3_256_eq` and its
siblings, `shake128_eq` and `shake256_eq`, prove FIPS 202's as SymCrypt's
Lean spec (`Rind/SymCrypt/Sha3.lean`, MIT) states it. Keccak-f is
s2n-bignum's `keccak 24` on lanes, the spec its routines' theorems state,
which `Rind/Keccak.lean` proves SymCrypt's KECCAK-f[1600].
`Rind/<Arch>/KeccakDispatch.lean` proves what rind's dispatch to the one-,
two-, and four-state routines computes, from those theorems. Each theorem
assumes `RunsSha3`: rind's entry guard and CPU checks pass. x86_64's AVX-512
eight-way Keccak, which ML-KEM's sampler runs, has
[its own quest](/quest/m4/verified/mlkem-avx512-sampler.md).

The portable backend's Keccak-f, which its SHA-3, ML-KEM, and ML-DSA run, in
`Rind/Portable/Keccak.lean`, over a translation of `low/portable/keccak.rs`
under `--cfg rind_portable`: `keccak_f1600_spec`, `keccak4_f1600_spec`, and
`keccak_nof4_f1600_spec` state what `Rind/<Arch>/KeccakDispatch.lean`'s do,
given FIPS 202's round constants and nothing of the CPU. Each round is
`keccak_round` written out, which `round_spec` proves by unfolding.

ML-KEM's polynomial arithmetic, against FIPS 203 as SymCrypt's Lean spec
(`Rind/SymCrypt/MlKem.lean`, MIT) states it, though not yet rind's Rust,
which has [its quest](/quest/m4/verified/mlkem-construction.md):

- `NTT_get`, `NTTInv_get` (`Rind/MlKem.lean`): Algorithms 9 and 10 compute
  the residues FIPS 203's Equations (4.12) and (4.13) define, and back;
- `forwardNtt_eq`, `inverseNtt_eq`, `mulcache_eq`, `basemul3Even_eq`,
  `basemul3Odd_eq`, and `tomont3329_eq` (`Rind/S2nMlKem.lean`): the specs
  s2n-bignum's aarch64 ML-KEM routines' theorems state are FIPS 203's `NTT`,
  its `NTTInv` times 2^16, and its `MultiplyNTTs` times 2^-16;
- `avx2ForwardNtt_eq`, `avx2InverseNtt_eq`, `avx2Mulcache_eq`, and
  `pmulaccred0K3_eq` and its siblings: the same for the x86_64 routines, which
  keep FIPS 203's coefficients in the AVX2 order.

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

AES-128, AES-192, and AES-256 on x86_64 CPUs with AES-NI and aarch64 CPUs
with the crypto extension, from `cipher::Aes` and the header-protection API's
`HeaderProtectionKey` to rind's key expansion and block cipher on the AES
instructions, in `Rind/X86_64/AesCipher.lean`, over each target's
`Rind/<Arch>/AesKey.lean`:

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

Each `AesKey.lean` also proves the decryption key `AesDecKey`, which AES-KW
unwraps with, against FIPS 197's equivalent inverse cipher, which
`Rind/AesInverse.lean` transliterates since Vale's spec only encrypts:

- `dec_key_new_spec`: a key of the algorithm's length holds `KeyExpansionEIC`'s
  round keys, reversed, which `invert_round_keys` computes from the cipher's;
- `hw_decrypt_block_spec`: the block becomes `EqInvCipher` of it under them.

`aesBlock`, `aesHeaderMask`, and `aesBlockDecrypt` are those specs on bytes,
which `#guard`s check against FIPS 197's and RFC 9001's vectors. The theorems
assume `RunsAesHw`, or for a key already made only its entry guard: rind's
CPU-feature checks find AES-NI, or on aarch64 the crypto extension, which no
input affects. AES-CBC decrypts through its own routines over the same round keys,
which [the AES modes quest](/quest/m4/verified/aes-modes.md) owns.

AES-128-GCM, AES-192-GCM, and AES-256-GCM on x86_64 CPUs with AES-NI and
PCLMULQDQ, from the AEAD API's `Key` down to HACL*'s Vale AES-GCM routines on
CPUs with AVX and MOVBE but no VAES, and to rind's own by-8 AES-CTR and GHASH
on CPUs without AVX and for what Vale's routines do not take, in
`Rind/X86_64/AesGcmAead.lean`:

- `aes_gcm_new`: a key that is not the algorithm's length is refused, and
  otherwise the key holds FIPS 197's round keys for its bytes, as Vale's
  `key_to_round_keys_LE` lays them out, and the GHASH key powers Vale's
  `hkeys_reqs_pub` requires of `E_K(0)`, or by-8's table of its first eight
  powers;
- `aes_gcm_seal`: for AAD under 2^61 bytes and messages up to 2^36 - 32
  bytes, the lengths rind takes, the ciphertext in place and the tag are
  Vale's `gcm_encrypt_LE` of the key, nonce, message, and AAD;
- `aes_gcm_seal_append_tag`: the same for a seal that appends the tag to any
  buffer: the ciphertext lands in the view its `as_mut` gives, and the call
  returns what its `extend` makes of that, handed the tag; and
  `aes_gcm_seal_append_tag_vec`: a `Vec<u8>` with room for the tag becomes
  the ciphertext followed by the tag, through `Rind/Core.lean`'s models of
  std's impls, which view the whole vector and append the tag as
  `extend_from_slice` does;
- `aes_gcm_open_separate_tag` and `aes_gcm_open`: for the same lengths, the
  call succeeds exactly when Vale's `gcm_decrypt_LE` accepts the tag, leaving
  its plaintext in place, and otherwise fails, leaving zeros.

Vale's `gcm_encrypt_LE` and `gcm_decrypt_LE` bound the AAD and message under
2^32 bytes, so `Rind/Vale.lean` transliterates them without it. Vale's
routines run seals of 129 bytes and more and AAD and messages under 2^32
bytes (`aes_gcm_encrypt_vale`, `aes_gcm_decrypt_vale` in
`Rind/X86_64/AesGcm.lean`), and by-8 the rest. `Rind/X86_64/AesGcmBy8.lean`
proves by-8, as `Rind/X86_64/AesGcmModel.lean` models it by hand, is Vale's `gctr_encrypt_LE` and `ghash_LE` without their bound:
its counter is the block's 64-bit halves swapped, which `PADDD` steps as
`inc32` does, its rounds FIPS 197's, and its GHASH the Horner rule on the
padded blocks, with the eight-block loop's sum of descending powers of the
key `Rind/X86_64/GhashClmul.lean` proves equal to it.
`Rind/X86_64/AesGcmClmul.lean` proves `tagged` is `gcm_encrypt_LE` and
`gcm_decrypt_LE` for a 96-bit nonce: the counter block is
`compute_iv_BE`'s, the length block `gcm_hash`'s, and the tag GCTR on the
hash under it, which by-8's `open` compares through `ct_equal`, so the opens
rest on `Rind/X86_64/CtEqual.lean`'s contracts too. AES-192 keys run by-8 on
both tiers, since Vale's routines take only AES-128 and AES-256
(`vale_192_none`). The key
setup is rind's: its AES-NI key expansion and block cipher, which
`Rind/X86_64/AesKey.lean` proves for AES header protection too, and its
PCLMULQDQ GHASH key powers, whose Karatsuba product and reduction
`Rind/Gf128.lean` proves to be Vale's `gf128_mul_rev` of the shifted keys
(`mul_shiftKey1`). Around Vale's routines, the Rust zero-pads the partial
blocks and picks the six-block loop's share, as EverCrypt's proven Low*
wrapper does. It pads them with GHASH's `load_partial` and `store_partial`,
whose overlapping loads and stores `Rind/X86_64/PartialBlock.lean` proves are
the bytes at every length. The theorems assume `RunsAesGcm`: rind's
CPU-feature checks pick Vale's tier (`RunsValeAesGcm`) or the SSE tier
(`RunsClmulAesGcm`), and the opens that `ct_equal`'s entry guard passes.
`Rind/X86_64/AeadDispatch.lean` models the AEAD API's function pointers
(`Algorithm`'s `expand` and `Sealer`'s `Ops`), and `seal_in_place_append_tag`,
which is generic over its buffer.

`aead::gcm::Key`, which takes an IV of any length and tags of any
`TagLength`, is proven on the same tiers, in `Rind/X86_64/GcmKey.lean`, a
hand model over `AeadDispatch` that quotes `rind/src/aead/gcm.rs`. Its `new`
for AES-128, AES-192, or AES-256 holds the `aead::Key` for the algorithm,
which refuses a key of another length (`gcm_key_new`). For an IV of 1 to
2^61 - 1 bytes and the same AAD and message lengths, its
`seal_in_place_separate_tag` leaves AES-GCM's ciphertext and returns the
first `tag_len` bytes of its tag (`gcm_key_seal`), and
`seal_in_place_append_tag` returns what its `extend` makes of that, handed
the tag (`gcm_key_seal_append_tag`), and `open_in_place` and
`open_in_place_separate_tag` succeed exactly when the tag is those bytes,
leaving the plaintext, and otherwise fail (`gcm_key_open`,
`gcm_key_open_separate_tag`). Only an authentication failure clears the
ciphertext to zeros; a refusal, of an input shorter than the tag or a
separate tag that is not the key's length, leaves the buffer unchanged. SP 800-38D's MSB_t truncation is the first bytes of Vale's tag, which
`gcmDecryptTrunc` compares. A seal under a 12-byte IV runs `aead::Key`'s path
and truncates its tag, and an open runs that path only under a 12-byte IV
with a 16-byte tag; the model's other arms run `AesGcm::encrypt_any` and `decrypt_any`, which
`Rind/X86_64/AesGcmAny.lean` proves: `initial_counter` is `compute_iv_BE`: the
96-bit counter block for a 12-byte IV, and otherwise the GHASH branch,
through by-8's table and the IV's length block, and the
tag's prefix is compared through `ct_equal`. They refuse an empty IV, one of
2^61 bytes or more, and AAD and messages past GCM's bounds with
`WrongLength`, leaving the buffer as it was (`check_gcm_iv_spec`,
`check_gcm_lengths_eq`), but those refusals are stated only for
`encrypt_any` and `decrypt_any`: the 96-bit path's theorems, and the
`gcm::Key` theorems above both, still take the AAD and message bounds as
hypotheses.
The AVX-512 tier's by-16 AES-CTR and GHASH, from 256 bytes to 2 KB, have no
proof yet: [the AVX-512 by-16 quest](/quest/m4/verified/aes-gcm-x86-intrinsics.md)
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
owns their HOL Light proofs, against `hol-light/s2n-bignum/common/chacha20poly1305.ml`,
which `Rind/S2nChaCha20Poly1305.lean` proves is `Rind/Spec.lean`'s RFC 8439
for a 32-byte key and a 12-byte nonce. CPUs without SSE4.1 run the separate ChaCha20
and Poly1305 passes, which the model leaves opaque. `AeadDispatch` models
`RandomizedNonceKey`, which reaches the system's random source, and
`Rind/ChaCha20Poly1305Test.lean` checks `Rind/Spec.lean`'s transliterations
against RFC 8439's and draft-irtf-cfrg-xchacha-03's test vectors.

RSASSA-PKCS1-v1_5 and RSASSA-PSS verification with SHA-256 on x86_64, from
the signature API's `PublicKey` to the Montgomery products, in
`Rind/X86_64/RsaDispatch.lean`, against RFC 8017 as `Rind/Rsa.lean`
transliterates it:

- `rsa_pkcs1_sha256_new_spec`, `rsa_pss_sha256_new_spec`: a key
  `PublicKey::new` returns for `verify::RSA_PKCS1_SHA256` or
  `RSA_PSS_SHA256` has a modulus N of 2048 to 8192 bits and an exponent E,
  and its `verify` accepts exactly the signatures RSASSA-PKCS1-V1_5-VERIFY
  accepts under (N, E) with SHA-256's `DigestInfo`, or RSASSA-PSS-VERIFY
  with MGF1-SHA-256 and a 32-byte salt;
- `rsa_pkcs1_sha256_from_components_spec`,
  `rsa_pss_sha256_from_components_spec`: the same for a key
  `PublicKey::from_components` returns, with N and E its components read
  big-endian;
- `rsa2048_mont_products`: on a CPU with BMI2 and ADX, a 2048-bit modulus's
  Montgomery products, s2n-bignum's Karatsuba routines and Montgomery
  reduction, return their results.

Below the API, `Rind/X86_64/RsaKey.lean` proves key loading
(`from_components_spec`): components with no leading zero byte, an odd
modulus of 1024 to 8192 bits, and an odd exponent from 3 to below 2^33 load,
and a loaded key holds them, with an odd modulus of 1024 to 8192 bits, an
odd exponent of at least 3, `pub_montifier`'s R^2 mod N, and
`mont_neg_inverse`'s -N^-1 mod 2^64.
`Rind/X86_64/RsaPublic.lean` proves the public operation's square-and-multiply
(`public_op_spec`), `Rind/X86_64/RsaBytes.lean` the conversions between
bytes and words, and `Rind/X86_64/{RsaVerify,RsaPss}.lean`
EMSA-PKCS1-v1_5's encoding check and EMSA-PSS-VERIFY. DER is opaque, as the ✓
leaves it out, so the `new` theorems hold for every key `PublicKey::new`
returns without saying which encodings it accepts. Each theorem assumes
`Runs`, `Sha256Blocks`, and messages of at most `maxInput` bytes, and each
that verifies takes `MontProducts k`, that `low::x86_64::mont`'s products
return their results at the modulus's width of k words.
`Rind/X86_64/RsaMont.lean`'s `mont_products` proves it at 16 and 32 words
with BMI2 and ADX, from s2n-bignum's theorems, and from `AwsLcMont`, that
aws-lc's unproven routines return theirs, at every other width and CPU.
`PublicKey` reaches each RSA algorithm's key parser and verification through
function pointers, which `Rind/X86_64/RsaDispatch.lean` models for these two
algorithms. On aarch64 the products are aws-lc's, so these proofs are not
copied there yet.

`admin/prove` fails if a hand model's quote no longer matches the source, if
the source names `Ops`, builds a `Masker`, or writes its `mask` outside the
dispatch models' quotes, if it builds a digest `Algorithm` outside
`DigestAlgorithm.lean`'s, if it mentions `Verification::Ed25519(` or
`Parsed::Ed25519(` outside `SignatureDispatch.lean`'s, or if it mentions
`Verification::Ecdsa(`, `EcdsaP256`, or `EcdsaKey::`, builds an `EcdsaOps` or
`EcdsaPair`, or reads an `ops` outside the signature models' quotes, or if it
mentions `Verification::Rsa(` or builds an `Rsa` outside them.

## Layout

- `hol-light/<arch>/`: rind's HOL Light proofs, one file per routine, and
  `hol-light/s2n-bignum/`, what they add to s2n-bignum: unmerged specs and
  rind's additions to the x86 model, with its cosimulation.
- `Rind/<Arch>/{Types,Funs}.lean`: Aeneas's translation, which `admin/prove`
  writes and git ignores.
- `Rind/<Arch>/{Types,Funs}External.lean` and `Rind/Core.lean`: what the
  translation leaves opaque, and models of the few standard-library items
  Aeneas's library lacks.
- `Rind/<Arch>/S2nBignum.lean`, `Rind/<Arch>/AwsLc.lean`, and
  `Rind/X86_64/ValeAesGcm.lean`: s2n-bignum's, aws-lc-verification's, and
  Vale's theorems, restated as axioms about the routines' Rust wrappers.
- `Rind/X86_64/Simd.lean`: models of the x86_64 intrinsics rind's AES,
  AES-GCM setup, partial blocks, and by-8 kernels call;
  `Rind/X86_64/AesGcmModel.lean`: a hand model, over those intrinsics, of its
  PCLMULQDQ GHASH and by-8 AES-GCM, whose raw pointers, `transmute`
  constants, `as_chunks`, and zipped iterators Aeneas cannot translate;
  `Rind/Aarch64/Neon.lean`, of the aarch64 intrinsics rind's AES calls, and
  `Rind/Aarch64/NeonVectors.lean`, the vectors `admin/neon-vectors.rs` tests
  them with; `Rind/Lanes.lean`, both targets' vector lanes and bytes.
- `Rind/Spec.lean` and `Rind/Bytes.lean`: the elliptic-curve, ChaCha20,
  Poly1305, and ChaCha20-Poly1305 specs and byte-conversion lemmas, and
  `Rind/ChaCha20Poly1305Test.lean`, the AEAD specs' known-answer tests; `Rind/Sha2.lean` and
  `Rind/Sha2Lemmas.lean`: SHA-512's, and `Rind/Sha2Test.lean`, its
  known-answer tests; `Rind/S2nSha512.lean`, s2n-bignum's SHA-512 spec,
  transliterated, and its proof that it is `Rind/Sha2.lean`'s;
  `Rind/Ed25519.lean`: Ed25519's;
  `Rind/HashSpec.lean`: SHA-1's, SHA-256's, HMAC's, HKDF's, and PBKDF2's, and
  `Rind/HashSpecTest.lean`, their known-answer tests; `Rind/Vale.lean`,
  `Rind/ValeBytes.lean`, and `Rind/Gf128.lean`: Vale's AES and GF(2^128) specs
  and their lemmas, and `Rind/AesInverse.lean`, FIPS 197's equivalent inverse
  cipher.
- `Rind/X86_64/{Dispatch,DigestDispatch,DigestAlgorithm,SignatureDispatch,AeadDispatch,HmacDispatch,GcmKey}.lean`:
  the hand models of the agreement, header-protection, digest, signature,
  AEAD, and HMAC APIs' dispatch, and of `aead::gcm::Key` over the AEAD model; `Rind/X86_64/HkdfExpand.lean` and
  `Rind/X86_64/Kdf/{TypesExternal,FunsExternal}.lean`, of what the HKDF and
  PBKDF2 pass leaves opaque.
- `Rind/X86_64/{X25519,Sha512,ChaCha20,Ed25519}.lean`: the X25519, SHA-512,
  ChaCha20, and Ed25519 proofs, `Rind/X86_64/{Blockwise,Sha,Hmac}.lean`,
  SHA-1's, SHA-256's, and HMAC's, and
  `Rind/X86_64/{DigestApi,HmacApi,Hkdf,Pbkdf2}.lean`, the digest, HMAC, HKDF,
  and PBKDF2 APIs'; `Rind/X86_64/HkdfAead.lean`, HKDF's conversion to AES-GCM
  and ChaCha20-Poly1305 keys, and `Rind/X86_64/HkdfAes.lean`, to AES
  header-protection keys; `Rind/Aes.lean`, FIPS 197's AES on bytes and its
  key schedule word by word; `Rind/<Arch>/AesKey.lean`, each target's key
  expansion and block cipher on the AES instructions;
  `Rind/X86_64/AesCipher.lean`, `cipher::Aes` and AES header protection, and
  `Rind/X86_64/{Ghash,PartialBlock,AesGcmGlue,AesGcm,GhashClmul,AesGcmBy8,AesGcmClmul,AesGcmAead,AesGcmAny}.lean`:
  the AES-GCM proof, on x86_64 alone; `Rind/X86_64/GcmKey.lean`, the hand model
  of `aead::gcm::Key` and its proofs; `Rind/X86_64/ChaCha20Poly1305.lean`, the
  ChaCha20-Poly1305 and XChaCha20-Poly1305 proof above aws-lc's routines.
- `Rind/Rsa.lean` and `Rind/RsaLemmas.lean`: RFC 8017's verification,
  transliterated, and its lemmas; `Rind/X86_64/{RsaBytes,RsaMont,RsaPublic,RsaKey,RsaVerify,RsaPss}.lean`:
  the RSA verification proof, on x86_64 alone, and
  `Rind/X86_64/RsaDispatch.lean`, the hand model of the signature API's RSA
  dispatch and its theorems.
- `Rind/SymCrypt/{Defs,Sha3}.lean`: SymCrypt's Lean FIPS 202 spec, vendored;
  `Rind/Keccak.lean`: s2n-bignum's Keccak spec, transliterated, and its proof
  that it is SymCrypt's; `Rind/Sha3.lean`: the sponge over bytes, and its
  proof that it is SymCrypt's; `Rind/KeccakStates.lean`: Keccak-f states as
  lanes, shared by `Rind/<Arch>/KeccakDispatch.lean`: rind's Keccak-f dispatch
  on each target, and `Rind/Portable/Keccak.lean`: the portable backend's
  Keccak-f; `Rind/X86_64/Sha3.lean`: the SHA-3 and
  SHAKE proofs.
- `Rind/SymCrypt/{NatBit,Round,Xof,MlKem,MlKemPolynomials,MlKemNtt}.lean`:
  SymCrypt's Lean FIPS 203 spec and its NTT lemmas, vendored;
  `Rind/MlKem.lean`: FIPS 203's NTT and inverse NTT in closed form;
  `Rind/S2nMlKem.lean`: s2n-bignum's ML-KEM specs, transliterated, and their
  proofs that they are FIPS 203's.
- `Rind/<Arch>/ShaBlocks.lean`: SHA-1 and SHA-256's block functions on each
  target, SHA-1's padded last blocks, and SHA-256's padded last blocks and
  finish; `Rind/Aarch64/Sha256Hw.lean`, the axiom for aarch64's routine with
  the SHA-256 instructions, and `Rind/S2nSha256.lean`, s2n-bignum's SHA-256
  spec, transliterated, and its proof that it is `Rind/HashSpec.lean`'s;
  `Rind/S2nChaCha20Poly1305.lean`, rind's HOL Light ChaCha20-Poly1305 spec,
  transliterated, and its proof that it is `Rind/Spec.lean`'s.
- `admin/prove` copies the other `Rind/X86_64/` models and proofs to
  `Rind/Aarch64/` with the target renamed.
- `Rind/NistGroup.lean`: that the NIST curves' `nist.add` is the addition of
  Mathlib's group of points on the curve; `Rind/NistOrder.lean`: that every
  finite point has order n, by counting the curve's points;
  `Rind/P256Group.lean`: that `p256` is prime, by a Pratt certificate;
  `Rind/N256Prime.lean`: that `n256` is prime; `Rind/P256Multiples.lean`: the
  group laws and multiples ECDSA's twin multiplication relies on.
- `Rind/X86_64/P256Dispatch.lean`, `Rind/X86_64/P256Agree.lean`,
  `Rind/Aarch64/P256Table.lean`, and `Rind/Aarch64/P256.lean`: the hand model
  of P-256's key generation, the P-256 agreement proof on both targets, and
  aarch64's generator table and key generation proofs.
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
  its HOL Light definition, transliterated, rather than opaque, so `nist.add`,
  `nist.pow`, and `nist.inv` in `Rind/Spec.lean` are trusted to be
  `weierstrass_add`, `group_pow`, and `ring_inv` on each NIST curve's group.
- That `Rind/SymCrypt/Sha3.lean` is FIPS 202, as SymCrypt's authors state,
  and that `Rind/Keccak.lean` transliterates s2n-bignum's `keccak_spec.ml`,
  in which the Keccak-f axioms state their results.
- That `Rind/SymCrypt/MlKem.lean` is FIPS 203, as SymCrypt's authors state,
  and that `Rind/S2nMlKem.lean` transliterates the s2n-bignum ML-KEM specs it
  names.
- That `Rind/Sha2.lean` restates cryptol-specs' SHA-512, its
  `processBlock_Common` as FIPS 180-4's, `Rind/S2nSha256.lean` and
  `Rind/S2nSha512.lean` transliterate s2n-bignum's SHA-256 and SHA-512 specs,
  and `Rind/S2nChaCha20Poly1305.lean` rind's HOL Light ChaCha20-Poly1305 spec.
- That `Rind/Rsa.lean` transliterates RFC 8017's RSASSA-PKCS1-v1_5 and
  RSASSA-PSS verification.
- That `Rind/Spec.lean`'s ChaCha20, Poly1305, and ChaCha20-Poly1305
  transliterate RFC 8439 and RFC 9001, its HChaCha20 and XChaCha20-Poly1305
  draft-irtf-cfrg-xchacha-03, its ECDSA FIPS 186-5, and
  `Rind/Ed25519.lean` RFC 8032 and s2n-bignum's encoding and decoding of
  edwards25519 points, whose `ed25519_decode` picks by Hilbert's choice as
  Lean's `Classical.epsilon` does.
- That `Rind/Vale.lean` transliterates Vale's AES and GF(2^128) specs and
  `hkeys_reqs_pub`, with the round functions Vale's AES spec assumes read as
  FIPS 197's, the S-box and `MixColumns` opaque.
- That `Rind/X86_64/Simd.lean`'s and `Rind/Aarch64/Neon.lean`'s intrinsics
  compute what their instructions do beyond the inputs they are tested on.
  `admin/simd-vectors.rs` runs each x86_64 instruction on the checking
  machine's CPU, on every immediate it reads, zero and all-ones lanes, and
  random inputs from a fixed seed, and Lean checks each model gives the
  same. `admin/neon-vectors.rs` does the same for the aarch64 ones; its
  output is committed as `Rind/Aarch64/NeonVectors.lean`, which Lean checks
  on any host, and the `prove` workflow reruns it on an aarch64 CPU and fails
  if the output changed. The AES models run the S-box and
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
