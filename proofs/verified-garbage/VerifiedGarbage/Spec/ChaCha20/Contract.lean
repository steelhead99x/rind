module

public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of ChaCha20's
streaming functions, in terms of `Spec/ChaCha20.lean`, for any target: `A`
is the target's calling convention. The signatures fix where the arguments
are, the memory each function may access, disjointness, and that the
pointers and lengths are public (see `TCB/Sig.lean`).

`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply` are the
cipher with the 16-byte nonce of `keystreamOf` (the initial block counter
and the RFC 8439 nonce), applied in pieces of any length, on a streaming
state (see `keyAt`, `leftAt`, `restAt`) that holds the key, the position in
the keystream and a partly used block. `init` makes the state represent the
whole keystream of a key and nonce, `set_nonce` that of another nonce with
the same key, and `apply` XORs the next bytes of it into data, or, if fewer
are left (the block counter would pass 2³² − 1), returns 0 and changes
nothing: so the caller keeps no count of its own. That keystream is RFC
8439's: it is `encrypt` (§2.4.1) of the 64 × (2³² − c) zero bytes, and
`encrypt` of any message not longer is that message XORed with its first
bytes.

The key, the nonce, the keystream and the data are secret. The number of
bytes of keystream left (`leftAt`) is not: `apply` may leak it (`leak`),
which an implementation needs to branch on the position within a block and
to check the length. It is 64 × (2³² − c) less the bytes applied since the
nonce was set, so it reveals the initial block counter `c` and the total
length applied: in RFC 8439 the block counter is public, as the nonce is
(§2.8 sends the nonce with the ciphertext and starts the counter at 1), and
the lengths of the pieces are public as every length is.

The streaming functions take the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (`stack`), and
`apply` may overwrite its arguments passed in memory (`writeArgs`), to pass
arguments to the functions it calls. Its implementations
for CPU features (e.g. `vg_chacha20_apply_avx2`) have the same contract.
-/

@[expose] public section

namespace VG.Spec.ChaCha20

/-- `vg_chacha20_init(state: *mut [u64; 96], key: *const [u8; 32], nonce: *const [u8; 16])`. -/
def initSig : Sig where
  params := [("state", .array true .u64 96), ("key", .array false .u8 32),
    ("nonce", .array false .u8 16)]

/-- Makes the streaming state at `state` hold the 32-byte key at `key` and
represent its whole keystream for the 16-byte nonce at `nonce`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A (post := fun state key nonce m m' _ =>
    keyAt m' state = bytesAt m key 32 ∧
      restAt m' state = keystreamOf (bytesAt m key 32) (bytesAt m nonce 16))
    (stack := stack)

/-- `vg_chacha20_init` on every target. -/
def initApi : Api where
  module := "chacha20"
  name := "vg_chacha20_init"
  sig := initSig
  contracts := some fun A stack => initContract A stack
  summary := "Starts a ChaCha20 keystream (RFC 8439 §2.4): makes the streaming state `*state` hold \
    the 32-byte key `*key` and the whole keystream for the 16-byte nonce `*nonce`, the initial \
    block counter `c` (4 bytes, little-endian) followed by the 12-byte RFC 8439 nonce: the blocks \
    for the counters `c` to 2³² − 1, 64 × (2³² − `c`) bytes.\n\n\
    Contract: `VG.Spec.ChaCha20.initContract`. The streaming state is opaque \
    (`VG.Spec.ChaCha20.keyAt`, `VG.Spec.ChaCha20.restAt`). Constant time: only the pointers may \
    affect timing, not the key or the nonce."
  safety := []

/-- `vg_chacha20_set_nonce(state: *mut [u64; 96], nonce: *const [u8; 16])`. -/
def setNonceSig : Sig where
  params := [("state", .array true .u64 96), ("nonce", .array false .u8 16)]

/-- Keeps the key of the streaming state at `state`, and makes it represent
the whole keystream of that key for the 16-byte nonce at `nonce`. -/
def setNonceContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  setNonceSig.contract A (post := fun state nonce m m' _ =>
    keyAt m' state = keyAt m state ∧
      restAt m' state = keystreamOf (keyAt m state) (bytesAt m nonce 16))
    (stack := stack)

/-- `vg_chacha20_set_nonce` on every target. -/
def setNonceApi : Api where
  module := "chacha20"
  name := "vg_chacha20_set_nonce"
  sig := setNonceSig
  contracts := some fun A stack => setNonceContract A stack
  summary := "Restarts a ChaCha20 keystream with the same key: makes the streaming state `*state` \
    represent the whole keystream of its key for the 16-byte nonce `*nonce` (as \
    `vg_chacha20_init` does), discarding what was left of the previous one.\n\n\
    Contract: `VG.Spec.ChaCha20.setNonceContract`. Constant time: only the pointers may affect \
    timing, not the key or the nonce."
  safety := []

/-- `vg_chacha20_apply(state: *mut [u64; 96], data: *mut u8, len: usize) -> u32`. -/
def applySig : Sig where
  params := [("state", .array true .u64 96), ("data", .slice true .u8 "len")]
  ret := some .u32

/-- If at least `len` bytes of keystream are left in the streaming state at
`state`, XORs the next `len` of them into the `len` bytes at `data`, leaves
the rest in the state, and returns 1. Otherwise returns 0, leaving the data
and what the state represents unchanged. The key is kept either way. May
leak the number of bytes of keystream left. -/
def applyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  applySig.contract A (post := fun state data len m m' r =>
    keyAt m' state = keyAt m state ∧
      if len.toNat ≤ leftAt m state then
        r = 1 ∧
          bytesAt m' data len.toNat =
            List.zipWith (· ^^^ ·) (bytesAt m data len.toNat) ((restAt m state).take len.toNat) ∧
          restAt m' state = (restAt m state).drop len.toNat
      else
        r = 0 ∧ bytesAt m' data len.toNat = bytesAt m data len.toNat ∧
          restAt m' state = restAt m state)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun state _data _len m => [leftAt m state])

/-- `vg_chacha20_apply` on every target. -/
def applyApi : Api where
  module := "chacha20"
  name := "vg_chacha20_apply"
  sig := applySig
  writeArgs := true
  contracts := some fun A stack => applyContract A stack
  summary := "Applies a ChaCha20 keystream (RFC 8439 §2.4), encrypting or decrypting: if at least \
    `len` bytes are left of the keystream that the streaming state `*state` represents, XORs the \
    next `len` of them into the `len` bytes at `data`, keeps the rest in `*state`, and returns 1. \
    Otherwise (the block counter would pass 2³² − 1) returns 0, and leaves the bytes at `data` \
    and the keystream unchanged.\n\n\
    Contract: `VG.Spec.ChaCha20.applyContract`. Constant time: only the pointers, `len` and the \
    number of bytes of keystream left in `*state` (`VG.Spec.ChaCha20.leftAt`: 64 × (2³² − `c`) \
    for the initial block counter `c`, less the bytes applied since) may affect timing, not the \
    key, the nonce, the keystream or the data. The function may leak that number."
  safety := []

end VG.Spec.ChaCha20
