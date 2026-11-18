module

public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA private keys' precomputed values

**Trusted** (as every file in `Spec/`). `vg_rsa_private_precompute`, in the
module `rsa`: the values of a private key's modulus and factors that the
private-key operations need and that do not depend on their input
(`privatePrecompute`), so that they are computed once, when the key is
loaded, and kept with the key, rather than at every operation.

The values are the modulus' (`publicPrecompute`: `n` and `R² mod n`, which
the check of each result against `e` needs), then `R_p² mod p` for the
Montgomery radix `R_p = 2^(64 w_p)` of `p`'s `w_p = max(2, ⌈p_len / 8⌉)`
words of 64 bits (`primeWords`, `primeR2`), and the same for `q`. The
operations given them (`vg_rsa_pss_sign_precomputed`,
`vg_rsa_pkcs1_sign_precomputed`, `vg_rsa_oaep_decrypt_precomputed`,
`vg_rsa_pkcs1_decrypt_precomputed`, in their padding schemes' files) compute
what the same operations without them compute, if they are given what
`vg_rsa_private_precompute` wrote for their key; an implementation uses
those of the values it needs, and may ignore the others.

Numbers are as in `Spec/Rsa/Contract.lean`. The modulus `n`, and so its
values, are public; `p` and `q`, and so `R_p² mod p` and `R_q² mod q`, are
secret.
-/

@[expose] public section

namespace VG.Spec.Rsa

/-! ## The values -/

/-- The words of 64 bits of the Montgomery radix of a factor of `len`
octets: `max(2, ⌈len / 8⌉)`. -/
def primeWords (len : Nat) : Nat := max 2 (modulusWords len)

/-- `R² mod p` for the factor `p` of `pB` and `R = 2^(64 w)`,
`w = primeWords pB.length`, as `w` words of 64 bits, least significant
first. -/
def primeR2 (pB : List Byte) : List (BitVec 64) :=
  toWords (2 ^ (128 * primeWords pB.length) % os2ip pB) (primeWords pB.length)

/-- The precomputed values of a private key with the factors `pB` and `qB`
of the modulus `nB` (`k` octets): `publicPrecompute nB`, then `primeR2 pB`
and `primeR2 qB`; or `none` if the modulus is not valid or `p q ≠ n`.

With `p q = n` for a valid (odd) modulus, `p` and `q` are odd, and so
`R² mod p` is what Montgomery arithmetic modulo `p` computes; with `p` and
`q` of fewer octets than `n`, as the functions take them, neither is 1. -/
def privatePrecompute (nB pB qB : List Byte) : Option (List (BitVec 64)) :=
  if os2ip pB * os2ip qB = os2ip nB then
    (publicPrecompute nB).map fun ws => ws ++ primeR2 pB ++ primeR2 qB
  else none

/-- The words of `privatePrecompute` for a modulus of `nLen` octets and
factors of `pLen` and `qLen`. -/
def privatePrecomputedWords (nLen pLen qLen : Nat) : Nat :=
  precomputedWords nLen + primeWords pLen + primeWords qLen

/-! ## For the operations given them -/

/-- The `# Safety` items of an operation given the precomputed values
`pre` of its key. -/
def privatePrecomputedSafety : List String :=
  ["`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
    "`pre` must hold what `vg_rsa_private_precompute` wrote for `n`, `p` and `q` (returning \
      1), and not have changed since."]

/-- The documentation of `pre`, for the summaries of the operations given
it. -/
def privatePrecomputedDoc : String :=
  "`pre` (`pre_len` words) must hold what `vg_rsa_private_precompute` wrote for `n`, `p` and \
    `q` (returning 1), as `n`, `p` and `q` must be valid"

/-- What an operation given `pre` may leak of it: the modulus' values, its
first `precomputedWords nLen` words. -/
def privatePrecomputedLeak (m : Mem) (pre : Addr) (nLen : Nat) : List Nat :=
  (wordsAt m pre (precomputedWords nLen)).map (·.toNat)

/-! ## `vg_rsa_private_precompute` -/

/-- `vg_rsa_private_precompute(pre: *mut u64, pre_len: usize, n: *const u8,
n_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def privatePrecomputeSig : Sig where
  params := [("pre", .slice true .u64 "pre_len"), ("n", .slice false .u8 "n_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- The precomputed values of the private key with the factors `p` and `q`
of the modulus `n` (`privatePrecompute`). Constant time but for `n`: in
particular, not whether `p q = n`. -/
def privatePrecomputeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  privatePrecomputeSig.contract A
    (pre := fun _pre preLen _n nLen _p pLen _q qLen _scratch scratchLen _ =>
      lenValid nLen.toNat ∧ 1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧
        qLen.toNat < nLen.toNat ∧
        preLen.toNat = privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat ∧
        scratchWords nLen.toNat ≤ scratchLen.toNat)
    (post := fun pre preLen n nLen p pLen q qLen _scratch _scratchLen m m' r =>
      match privatePrecompute (bytesAt m n nLen.toNat) (bytesAt m p pLen.toNat)
          (bytesAt m q qLen.toNat) with
      | some ws => r = 1 ∧ wordsAt m' pre preLen.toNat = ws
      | none => r = 0 ∧ wordsAt m' pre preLen.toNat = List.replicate preLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _pre _preLen n nLen _p _pLen _q _qLen _scratch _scratchLen m =>
      (bytesAt m n nLen.toNat).map (·.toNat))

def privatePrecomputeApi : Api where
  module := "rsa"
  name := "vg_rsa_private_precompute"
  sig := privatePrecomputeSig
  writeArgs := true
  contracts := some fun A stack => privatePrecomputeContract A stack
  summary := "The values of an RSA private key that its operations need and that do not \
    depend on their input, so that they are computed once per key rather than once per \
    operation: what the `_precomputed` private-key operations take. With the modulus `n` \
    (`n_len` bytes, most significant first, odd, from 512 to 8192 bits, its first byte not \
    zero) of `w = ⌈n_len / 8⌉` words of 64 bits, and the factors `p` (`p_len` bytes) and \
    `q` (`q_len` bytes), most significant first, writes to `pre`, least significant word \
    first: `n` and `R² mod n` for `R = 2^(64 w)` (`w` words each, what \
    `vg_rsa_public_precompute` writes), then `R_p² mod p` for `R_p = 2^(64 w_p)` and \
    `w_p = max(2, ⌈p_len / 8⌉)` (`w_p` words), then the same for `q`; and returns 1. \
    Writes zeros and returns 0 if `n` is not such a modulus or `p q ≠ n`. The rest of the \
    key is checked when it is loaded (`vg_rsa_check_key`).\n\n\
    Contract: `VG.Spec.Rsa.privatePrecomputeContract`. Constant time but for the modulus: \
    timing may depend on the pointers, the lengths and the contents of `n`, not on `p` or \
    `q`."
  safety := ["`n_len` must be in 64..=1024.", "`p_len` and `q_len` must be in 1..`n_len`.",
    "`pre_len` must be `2 * ⌈n_len / 8⌉ + max(2, ⌈p_len / 8⌉) + max(2, ⌈q_len / 8⌉)`.",
    "The contents of `pre` are secret (they are values of `p` and `q`); the caller must \
      destroy them after use."] ++ scratchSafety

end VG.Spec.Rsa
