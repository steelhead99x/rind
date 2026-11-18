module

public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.Artifact

/-!
# RSA primitives: the contracts, on every target

**Trusted** (as every file in `Spec/`). In the module `rsa`:

* `vg_rsa_public_precompute`: the values of a public key's modulus that
  RSAEP needs (`Rsa.publicPrecompute`), to be kept with the key;
* `vg_rsa_crt_values`: the CRT values `(dP, dQ, qInv)` of the private key
  `(p, q, d)` (`Rsa.crtKey`);
* `vg_rsa_check_key`: BoringSSL's `RSA_check_key` of the private key
  `(n, e, d, p, q, dP, dQ, qInv)` (`Rsa.checkKey`).

A private key is brought to the CRT form once, when it is loaded, and every
operation on it is checked against the public exponent as BoringSSL checks
it (`Rsa.privateChecked`, `writtenOutcome`). The RSA public-key and checked
private-key operations themselves, `vg_rsa_public_precomputed_checked` and
`vg_rsa_private_checked`, are internal functions, which only the padding
schemes' verified functions call: their contracts are in
`Proof/Rsa/Contract.lean`, untrusted.

Every number is a slice of octets, most significant first, with a length of
its own (a `Sig` slice carries its own length). The modulus `n` is `n_len`
octets, from 64 to 1024, and so are the input and the output, and the
factors `vg_rsa_recover_primes_det` writes (`Rsa/RecoverDet.lean`); `e` and `d` are at most `n_len`
octets; `p` and its values (`dP`, `qInv`) are `p_len` octets, and `q` and
`dQ` are `q_len` octets, each below `n_len`. These are preconditions, on the
public lengths; everything about the values is checked: the function returns
1 and writes its results, or returns 0 and writes zeros (but
`vg_rsa_check_key`, which writes nothing).

The signature determines memory validity, separation and that the pointers
and lengths are public, through `Sig.contract`. The public key, `n` and `e`,
is public too, and may affect timing (`leak`): an implementation may, for
instance, branch on the bits of `e`. The input is secret (RSAEP may encrypt
a secret), and so is every part of a private key. The return
value depends on secrets (whether the input is below `n`, and whether the
private key is consistent).

`scratch` is working space of at least `16 n_len + 32` `u64`s, or, for the
public-key functions (`vg_rsa_public_precompute` and the internal
`vg_rsa_public_precomputed_checked`), `8 ⌈n_len / 8⌉ + 48`, whose
contents on return are unspecified. `stack` is the number of bytes below the stack
pointer that an implementation's calls and frames use. The functions may
overwrite their arguments passed in memory, where the calling convention
allows it (`writeArgs`).
-/

@[expose] public section

namespace VG.Spec.Rsa

/-- The bytes at `p`, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- The least working space, in `u64`s, for a modulus of `nLen` octets. -/
def scratchWords (nLen : Nat) : Nat := 16 * nLen + 32

/-- The least working space, in `u64`s, of the public-key functions for a
modulus of `nLen` octets: a header of 32 words and 8 numbers of
`⌈nLen / 8⌉ + 2` words. -/
def publicScratchWords (nLen : Nat) : Nat := 8 * modulusWords nLen + 48

/-- The bounds on the modulus' length, in octets. -/
def lenValid (nLen : Nat) : Prop := 64 ≤ nLen ∧ nLen ≤ 1024

/-- The postcondition of a function returning `res`, `nLen` octets or
`none`, at `out`. -/
def written (m' : Mem) (out : Addr) (nLen : Nat) (r : BitVec 32) : Option (List Byte) → Prop
  | some y => r = 1 ∧ bytesAt m' out nLen = y
  | none => r = 0 ∧ bytesAt m' out nLen = List.replicate nLen 0

/-- The postcondition of a function returning `res`, octet strings or `none`,
at the addresses and lengths `outs`: each string at its address, or zeros
at all of them. -/
def writtenAll (m' : Mem) (outs : List (Addr × Nat)) (r : BitVec 32) : Option (List (List Byte)) → Prop
  | some ys => r = 1 ∧ outs.map (fun o => bytesAt m' o.1 o.2) = ys
  | none => r = 0 ∧ ∀ o ∈ outs, bytesAt m' o.1 o.2 = List.replicate o.2 0

/-- The `n` words of 64 bits at `p`. -/
def wordsAt (m : Mem) (p : Addr) (n : Nat) : List (BitVec 64) :=
  (List.range n).map fun i => m.readW (p + BitVec.ofNat 64 (8 * i)) 64

/-- The words of the precomputed values of a modulus of `nLen` octets
(`publicPrecompute`). -/
def precomputedWords (nLen : Nat) : Nat := 2 * modulusWords nLen

/-- The `# Safety` items on the working space. -/
def scratchSafety : List String :=
  ["`scratch_len` must be at least `16 * n_len + 32`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-- The `# Safety` items on the working space of the public-key functions. -/
def publicScratchSafety : List String :=
  ["`scratch_len` must be at least `8 * ⌈n_len / 8⌉ + 48`.",
    "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
      must destroy them after use."]

/-! ## `vg_rsa_public_precompute` -/

/-- `vg_rsa_public_precompute(pre: *mut u64, pre_len: usize, n: *const u8,
n_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def publicPrecomputeSig : Sig where
  params := [("pre", .slice true .u64 "pre_len"), ("n", .slice false .u8 "n_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The precomputed values of the modulus `n` (`publicPrecompute`). Timing
may depend on `n`, which is public. -/
def publicPrecomputeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicPrecomputeSig.contract A
    (pre := fun _pre preLen _n nLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ preLen.toNat = precomputedWords nLen.toNat ∧
        publicScratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun pre preLen n nLen _scratch _scratchLen m m' r =>
      match publicPrecompute (bytesAt m n nLen.toNat) with
      | some ws => r = 1 ∧ wordsAt m' pre preLen.toNat = ws
      | none => r = 0 ∧ wordsAt m' pre preLen.toNat = List.replicate preLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _pre _preLen n nLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def publicPrecomputeApi : Api where
  module := "rsa"
  name := "vg_rsa_public_precompute"
  sig := publicPrecomputeSig
  writeArgs := true
  contracts := some fun A stack => publicPrecomputeContract A stack
  summary := "The values of an RSA modulus that `vg_rsa_public_precomputed_checked` takes, \
    so that they are computed once per public key rather than once per operation. With the modulus \
    `n` (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its first byte \
    not zero) of `w = ⌈n_len / 8⌉` words of 64 bits, writes `n` and then `R² mod n` for \
    `R = 2^(64 w)` to `pre` (`w` words each, least significant first) and returns 1; or \
    writes zeros and returns 0 if `n` is not such a modulus.\n\n\
    Contract: `VG.Spec.Rsa.publicPrecomputeContract`. Timing may depend on the pointers, \
    the lengths and the contents of `n`."
  safety := ["`n_len` must be in 64..=1024.", "`pre_len` must be `2 * ⌈n_len / 8⌉`."] ++
    publicScratchSafety

/-! ## `vg_rsa_crt_values` -/

/-- `vg_rsa_crt_values(dp: *mut u8, dp_len: usize, dq: *mut u8,
dq_len: usize, qinv: *mut u8, qinv_len: usize, n: *const u8, n_len: usize,
p: *const u8, p_len: usize, q: *const u8, q_len: usize, d: *const u8,
d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def crtValuesSig : Sig where
  params := [("dp", .slice true .u8 "dp_len"), ("dq", .slice true .u8 "dq_len"),
    ("qinv", .slice true .u8 "qinv_len"), ("n", .slice false .u8 "n_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("d", .slice false .u8 "d_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The CRT values of the private key `(p, q, d)` of the modulus `n`
(`crtKey`). Constant time but for `n`. -/
def crtValuesContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  crtValuesSig.contract A
    (pre := fun _dp dpLen _dq dqLen _qinv qinvLen _n nLen _p pLen _q qLen _d dLen _scratch
        scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧
        qLen.toNat < nLen.toNat ∧ dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧
        dqLen.toNat = qLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun dp _dpLen dq _dqLen qinv _qinvLen n nLen p pLen q qLen d dLen _scratch
        _scratchLen m m' r =>
      writtenAll m' [(dp, pLen.toNat), (dq, qLen.toNat), (qinv, pLen.toNat)] r
        ((crtKey (bytesAt m n nLen.toNat) (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat)
          (bytesAt m d dLen.toNat)).map fun v => [v.1, v.2.1, v.2.2]))
    (writeArgs := true) (stack := stack)
    (leak := some fun _dp _dpLen _dq _dqLen _qinv _qinvLen n nLen _p _pLen _q _qLen _d _dLen
        _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def crtValuesApi : Api where
  module := "rsa"
  name := "vg_rsa_crt_values"
  sig := crtValuesSig
  writeArgs := true
  contracts := some fun A stack => crtValuesContract A stack
  summary := "The CRT values of an RSA private key `(p, q, d)` (SP 800-56B Rev. 2 §6.2.2's \
    prime-factor format), which bring it to the CRT format `(p, q, dP, dQ, qInv)` that \
    `vg_rsa_private_checked` takes: `dP = d mod (p - 1)`, `dQ = d mod (q - 1)` and \
    `qInv = q⁻¹ mod p` (§6.2.2's CRT format). With the modulus `n` (`n_len` bytes, most \
    significant first, odd, from 512 to 8192 bits, its first byte not zero), `p` (`p_len` \
    bytes), `q` (`q_len` bytes) and `d` (`d_len` bytes), all most significant first, writes \
    `dP` to `dp` and `qInv` to `qinv` (`p_len` bytes each) and `dQ` to `dq` (`q_len` bytes), \
    most significant first, and returns 1; or writes zeros to all three and returns 0 if `n` \
    is not such a modulus, `p q ≠ n`, or `q` has no inverse modulo `p`. Nothing checks that \
    `p` and `q` are prime or that `d` is the key's private exponent.\n\n\
    Contract: `VG.Spec.Rsa.crtValuesContract`. Constant time but for the modulus: timing \
    may depend on the pointers, the lengths and the contents of `n`, not on the private key."
  safety := ["`n_len` must be in 64..=1024.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`.",
    "`d_len` must be in 1..=`n_len`."] ++ scratchSafety

/-! ## BoringSSL's checks

What BoringSSL checks (`Rsa.publicOpChecked`, `Rsa.privateChecked`,
`Rsa.checkKey`), for the contracts of the RSA functions here and in the
padding schemes' files. -/

/-- The public exponent and its limits, in the summaries. -/
def exponentDoc : String :=
  "the public exponent `e` (`e_len` bytes, most significant first, odd, from 3 to \
    `2^33 - 1`: BoringSSL's limits)"

/-! ### The outcome of a checked private-key operation -/

/-- The postcondition of a function with the outcome `o` (`Outcome`) of
`nLen` octets at `out`: 1 and the result, 0 and zeros if the key or the
input is refused, or 2 and zeros on the internal error. -/
def writtenOutcome (m' : Mem) (out : Addr) (nLen : Nat) (r : BitVec 32) : Outcome → Prop
  | .ok y => r = 1 ∧ bytesAt m' out nLen = y
  | .invalid => r = 0 ∧ bytesAt m' out nLen = List.replicate nLen 0
  | .fault => r = 2 ∧ bytesAt m' out nLen = List.replicate nLen 0

/-! ### `vg_rsa_check_key` -/

/-- `vg_rsa_check_key(n: *const u8, n_len: usize, e: *const u8, e_len: usize,
d: *const u8, d_len: usize, p: *const u8, p_len: usize, q: *const u8,
q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, scratch: *mut u64,
scratch_len: usize) -> u32`. -/
def checkKeySig : Sig where
  params := [("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("d", .slice false .u8 "d_len"), ("p", .slice false .u8 "p_len"),
    ("q", .slice false .u8 "q_len"), ("dp", .slice false .u8 "dp_len"),
    ("dq", .slice false .u8 "dq_len"), ("qinv", .slice false .u8 "qinv_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- BoringSSL's `RSA_check_key` of the private key
`(n, e, d, p, q, dP, dQ, qInv)` (`checkKey`): 1 if it accepts the key, 0 if
not. Constant time but for the public key. -/
def checkKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  checkKeySig.contract A
    (pre := fun _n nLen _e eLen _d dLen _p pLen _q qLen _dp dpLen _dq dqLen _qinv qinvLen
        _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧
        1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
        1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
        dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun n nLen e eLen d dLen p pLen q qLen dp _dpLen dq _dqLen qinv _qinvLen _scratch
        _scratchLen m _m' r =>
      r = if checkKey (bytesAt m n nLen.toNat) (bytesAt m e eLen.toNat) (bytesAt m d dLen.toNat)
          (bytesAt m p pLen.toNat) (bytesAt m q qLen.toNat) (bytesAt m dp pLen.toNat)
          (bytesAt m dq qLen.toNat) (bytesAt m qinv pLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun n nLen e eLen _d _dLen _p _pLen _q _qLen _dp _dpLen _dq _dqLen _qinv
        _qinvLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat ++ bytesAt m e eLen.toNat).map (·.toNat))

def checkKeyApi : Api where
  module := "rsa"
  name := "vg_rsa_check_key"
  sig := checkKeySig
  writeArgs := true
  contracts := some fun A stack => checkKeyContract A stack
  summary := "Checks an RSA private key `(n, e, d, p, q, dP, dQ, qInv)` exactly as \
    BoringSSL's `RSA_check_key` does. With the modulus `n` (`n_len` bytes), the public \
    exponent `e` (`e_len` bytes), the private exponent `d` (`d_len` bytes), `p`, `dp` and \
    `qinv` (`p_len` bytes) and `q` and `dq` (`q_len` bytes), all most significant first, \
    returns 1 if `n` is odd, from 512 to 8192 bits and its first byte not zero, `e` is odd \
    and from 3 to `2^33 - 1`, `d < n`, `p < n`, `q < n`, `p q = n`, \
    `d e ≡ 1 (mod p - 1)`, `d e ≡ 1 (mod q - 1)`, `dP < p - 1`, `e dP ≡ 1 (mod p - 1)`, \
    `dQ < q - 1`, `e dQ ≡ 1 (mod q - 1)`, `qInv < p` and `q qInv ≡ 1 (mod p)`; and 0 \
    otherwise. Like `RSA_check_key`, it does not check that `p` and `q` are prime; if they \
    are, `vg_rsa_private_checked` never returns its internal error for a key it accepts.\n\n\
    Contract: `VG.Spec.Rsa.checkKeyContract`. Constant time but for the public key: timing \
    may depend on the pointers, the lengths and the contents of `n` and `e`, not on the \
    private key."
  safety := ["`n_len` must be in 64..=1024.", "`e_len` and `d_len` must be in 1..=`n_len`.",
    "`p_len` and `q_len` must be in 1..`n_len`.",
    "`dp_len` and `qinv_len` must be `p_len`, and `dq_len` must be `q_len`."] ++ scratchSafety

end VG.Spec.Rsa
