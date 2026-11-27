module

public import VerifiedGarbage.Spec.Hmac
public import VerifiedGarbage.TCB.Artifact

/-!
# HMAC over any streaming hash function: the contracts, on every target

**Trusted** (as every file in `Spec/`). An HMAC computation with the hash
function `H` is two streaming states of `H`: the inner one, which absorbs
`(K₀ ⊕ ipad) ‖ text`, and the outer one, which holds `K₀ ⊕ opad`. `init`
sets them up from the key, the text is absorbed into the inner state with
`H`'s own `update`, and `finalize` computes the MAC. The hash function is a
parameter (`StreamingHash`), so that one implementation, calling the
verified streaming functions of `H`, serves every hash function.

`finalize` writes the MAC through an `out` pointer on every target.

An `Instance` is a hash function as the Rust interface has it: the names of
its functions `vg_hmac_<hash>_init` and `vg_hmac_<hash>_finalize` (and
`vg_pbkdf2_hmac_<hash>_iterate` and `vg_pbkdf2_hmac_<hash>`,
`Spec/Pbkdf2/Generic.lean`), their working space, and their documentation
(`Instance.initAnyKeyApi`, `Instance.finalizeApi`). Every hash function,
SHA-256 included, is an `Instance`, and a new one needs nothing else.

`vg_hmac_<hash>_init` (`Instance.initAnyKeyApi`) has the contract
`initAnyKeyContract`: it takes a key of any length and does all of FIPS
198-1 §4's steps 1–3 (`blockKey`), hashing a long key with the verified
streaming functions of `H` in more working space
(`Instance.initAnyKeyScratch`). `initContract` takes a key of at most a
block and leaves step 2 (hashing a longer key) to its caller: no `Api` has
it, only functions the verified code calls internally.

`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the rest. `stack` is the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (see `Sig.contract`): `init`
and `finalize` keep their working space there. The functions may overwrite
their arguments passed in memory, where
the calling convention allows it (`writeArgs`), to pass arguments to the
functions they call.
-/

@[expose] public section

namespace VG.Spec.Hmac

open Sha256 (bytesAt)

/-- A hash function with a streaming (incremental) implementation, as the
HMAC and PBKDF2 contracts use it: the hash function itself, the size in
bytes of its streaming state and of its digest, and what it means for the
streaming state at an address to represent a message (the `Repr` of its
`init`, `update` and `finalize` contracts). -/
structure StreamingHash where
  H : HashFunction
  stateBytes : Nat
  digestBytes : Nat
  Repr : Mem → Addr → List Byte → Prop

/-- SHA-256: the 96-byte streaming state of `Spec/Sha256/Contract.lean`. -/
def sha256S : StreamingHash := ⟨sha256, 96, 32, Sha256.Repr⟩

/-- SHA-224: SHA-256's 96-byte streaming state, from SHA-224's initial hash
value (`vg_sha224_init`, then SHA-256's `update` and `finalize`). -/
def sha224S : StreamingHash := ⟨sha224, 96, 28, Sha256.ReprFrom Sha256.H0_224⟩

/-- SHA-1: the 84-byte streaming state of `Spec/Sha1/Contract.lean`. -/
def sha1S : StreamingHash := ⟨sha1, 84, 20, Sha1.Repr⟩

/-- MD5: the 80-byte streaming state of `Spec/Md5/Contract.lean`. -/
def md5S : StreamingHash := ⟨md5, 80, 16, Md5.Repr⟩

/-- SHA-384: the 192-byte streaming state of `Spec/Sha512/Contract.lean`,
from SHA-384's initial hash value. -/
def sha384S : StreamingHash := ⟨sha384, 192, 48, Sha512.Repr Sha512.H0_384⟩

/-- SHA-512: as SHA-384, from SHA-512's initial hash value. -/
def sha512S : StreamingHash := ⟨sha512, 192, 64, Sha512.Repr Sha512.H0_512⟩

/-- SHA-512/224: as SHA-384, from SHA-512/224's initial hash value. -/
def sha512_224S : StreamingHash := ⟨sha512_224, 192, 28, Sha512.Repr Sha512.H0_512_224⟩

/-- SHA-512/256: as SHA-384, from SHA-512/256's initial hash value. -/
def sha512_256S : StreamingHash := ⟨sha512_256, 192, 32, Sha512.Repr Sha512.H0_512_256⟩

variable (S : StreamingHash) (scratch : Nat)

/-- `vg_hmac_<hash>_init(inner: *mut [u8; S], outer: *mut [u8; S], key: *const u8, key_len: usize)`,
with `S` the size of the streaming state. -/
def initSig : Sig where
  params := [("inner", .array true .u8 S.stateBytes), ("outer", .array true .u8 S.stateBytes),
    ("key", .slice false .u8 "key_len")]

/-- `init`'s precondition, for a key of at most the block size of `H`. -/
def initPre (pb : Nat) : Curry ((initSig S).words pb) (Mem → Prop) :=
  fun _inner _outer _key keyLen _ => keyLen.toNat ≤ S.H.blockSize

/-- Makes the streaming state at `inner` represent `K₀ ⊕ ipad` and the one at
`outer` represent `K₀ ⊕ opad`, for the key `K₀` made from the `key_len` bytes
at `key` by FIPS 198-1 §4's steps 1–3 (`blockKey`). -/
def initPost (pb : Nat) : (initSig S).Post pb := fun inner outer key keyLen m m' _ =>
  let k0 := blockKey S.H (bytesAt m key keyLen.toNat)
  S.Repr m' inner (xorPad k0 ipad) ∧ S.Repr m' outer (xorPad k0 opad)

/-- For a key of at most the block size of `H`: `initPost`. The key is
secret. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (initSig S).contract A (pre := initPre S A.ptrBits) (post := initPost S A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- For a key of any length: `initPost`, for the key `K₀` made from the
`key_len` bytes at `key` by FIPS 198-1 §4's steps 1–3 (`blockKey`: hashed
with `H` if longer than the block size of `H`, then padded with zeros to the
block size). The key is secret. -/
def initAnyKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (initSig S).contract A (post := initPost S A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_hmac_<hash>_finalize(inner: *mut [u8; S], outer: *const [u8; S], count: u64, out: *mut [u8; D])`,
with `S` the size of the streaming state and `D` that of the digest. `count`
is public; `inner` is left unspecified. -/
def finalizeSig : Sig where
  params := [("inner", .array true .u8 S.stateBytes), ("outer", .array false .u8 S.stateBytes),
    ("count", .int .u64 true), ("out", .array true .u8 S.digestBytes)]

/-- If, for a key `K₀` of the block size of `H` and a text of fewer than
2⁶⁴ bytes with the key, the streaming state at `inner` represents
`(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at `outer`
represents `K₀ ⊕ opad`, writes the HMAC of the text under `K₀` to `out`. -/
def finalizePost (pb : Nat) : (finalizeSig S).Post pb := fun inner outer count out m m' _ =>
  ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr m inner (xorPad k0 ipad ++ text) →
    count = BitVec.ofNat 64 (S.H.blockSize + text.length) → S.Repr m outer (xorPad k0 opad) →
    bytesAt m' out S.digestBytes = hmacBlockKey S.H k0 text

/-- `finalizePost`. The states are secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (finalizeSig S).contract A (post := finalizePost S A.ptrBits) (writeArgs := true) (stack := stack)

/-! ## The functions in the Rust interface -/

/-- A streaming hash function's HMAC functions in the Rust interface (and
its PBKDF2 function, `Instance.pbkdf2Api`): the
hash function, its name (`SHA-1`), the name that stands for it in the Rust
names (`vg_hmac_sha1_init`), the Lean name of this record (for the
documentation), the Rust name of its streaming `update` function, which the
documentation points the caller to, and the number of 64-bit words of
working space of each HMAC function and of the PBKDF2 iteration, which
leaves room for the working space of the functions it calls and for its own
spills (`init` for a key of any length and the whole of PBKDF2 have more,
`Instance.initAnyKeyScratch` and `Instance.pbkdf2Scratch`). -/
structure Instance where
  S : StreamingHash
  alg : String
  rust : String
  lean : String
  update : String
  scratch : Nat

/-- SHA-256: `vg_sha256_update` needs 76 words of working space, of the 104
given. -/
def sha256I : Instance :=
  ⟨sha256S, "SHA-256", "sha256", "sha256I", "vg_sha256_update", 104⟩

/-- SHA-224: as SHA-256, whose `vg_sha256_update` it absorbs the text with. -/
def sha224I : Instance :=
  ⟨sha224S, "SHA-224", "sha224", "sha224I", "vg_sha256_update", 104⟩

/-- SHA-1: `vg_sha1_update` needs 20 words of working space. -/
def sha1I : Instance := ⟨sha1S, "SHA-1", "sha1", "sha1I", "vg_sha1_update", 56⟩

/-- MD5: `vg_md5_update` needs 14 words of working space. -/
def md5I : Instance := ⟨md5S, "MD5", "md5", "md5I", "vg_md5_update", 48⟩

/-- SHA-384: `vg_sha512_update` needs 172 words of working space; 62 more
are left for the HMAC and PBKDF2 functions' own registers and buffers
(AArch64's PBKDF2 iteration, which keeps the most, uses 47: its caller's
registers and its return address, a streaming state and two final hash
values). -/
def sha384I : Instance :=
  ⟨sha384S, "SHA-384", "sha384", "sha384I", "vg_sha512_update", 234⟩

/-- SHA-512: as SHA-384. -/
def sha512I : Instance :=
  ⟨sha512S, "SHA-512", "sha512", "sha512I", "vg_sha512_update", 234⟩

/-- SHA-512/224: as SHA-384. -/
def sha512_224I : Instance :=
  ⟨sha512_224S, "SHA-512/224", "sha512_224", "sha512_224I", "vg_sha512_update", 234⟩

/-- SHA-512/256: as SHA-384. -/
def sha512_256I : Instance :=
  ⟨sha512_256S, "SHA-512/256", "sha512_256", "sha512_256I", "vg_sha512_update", 234⟩

namespace Instance

variable (I : Instance)

/-- The contract of `vg_hmac_<hash>_init`: `VG.Spec.Hmac.initContract`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Hmac.initContract I.S A stack

/-- The contract of `vg_hmac_<hash>_finalize`: `VG.Spec.Hmac.finalizeContract`. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Hmac.finalizeContract I.S A stack

/-- The number of 64-bit words of working space of `vg_hmac_<hash>_init`
for a key of any length (`initAnyKeyContract`), which an implementation keeps
on its stack: that of the HMAC functions (`scratch`, which holds the working
space of `H`'s `update` and `finalize`), then a word for each byte of the
streaming state, for hashing a key longer than a block (a streaming state
and the digest), for the padded keys and for spills. It is the working space
of `vg_pbkdf2_hmac_<hash>` (`Instance.pbkdf2Scratch`), which hashes a long
password likewise. -/
def initAnyKeyScratch : Nat := I.scratch + I.S.stateBytes

/-- The contract of `vg_hmac_<hash>_init` for a key of any length:
`VG.Spec.Hmac.initAnyKeyContract`. -/
def initAnyKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Hmac.initAnyKeyContract I.S A stack

/-- `vg_hmac_<hash>_init`, for a key of any length, on every target. -/
def initAnyKeyApi : Api where
  module := s!"hmac_{I.rust}"
  name := s!"vg_hmac_{I.rust}_init"
  sig := initSig I.S
  writeArgs := true
  contracts := some fun A stack => I.initAnyKeyContract A stack
  summary := s!"Starts an HMAC-{I.alg} computation with a key of any length: makes the {I.alg} \
    streaming state `*inner` represent `K₀ ⊕ ipad` and `*outer` represent `K₀ ⊕ opad`, where \
    `K₀` is the `key_len` bytes at `key` (or their {I.alg} digest, if there are more than \
    {I.S.H.blockSize}) padded with zeros to {I.S.H.blockSize} bytes (FIPS 198-1 §4, steps 1–3). \
    The text is then absorbed with `{I.update}` on `*inner` (its `count` starting at \
    {I.S.H.blockSize}), and the MAC computed with `vg_hmac_{I.rust}_finalize`.\n\n\
    Contract: `VG.Spec.Hmac.Instance.initAnyKeyContract` of `VG.Spec.Hmac.{I.lean}`. Constant \
    time: only the pointers and `key_len` may affect timing, not the key."
  safety := []

/-- `vg_hmac_<hash>_finalize` on every target. -/
def finalizeApi : Api where
  module := s!"hmac_{I.rust}"
  name := s!"vg_hmac_{I.rust}_finalize"
  sig := finalizeSig I.S
  writeArgs := true
  contracts := some fun A stack => I.finalizeContract A stack
  summary := s!"Finishes an HMAC-{I.alg} computation: if, for a {I.S.H.blockSize}-byte key `K₀` \
    and a text of fewer than 2⁶⁴ − {I.S.H.blockSize} bytes, the {I.alg} streaming state `*inner` \
    represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes, and `*outer` represents `K₀ ⊕ opad`, \
    writes the HMAC-{I.alg} of the text under `K₀` ({I.S.digestBytes} bytes) to `*out`.\n\n\
    Contract: `VG.Spec.Hmac.Instance.finalizeContract` of `VG.Spec.Hmac.{I.lean}`. Constant \
    time: only the pointers and `count` may affect timing, not the states."
  safety := ["The contents of `inner` on return are unspecified."]

end Instance

end VG.Spec.Hmac
