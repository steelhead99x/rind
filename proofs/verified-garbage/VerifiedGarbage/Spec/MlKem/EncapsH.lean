module

public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Spec.Zeroize

/-!
# ML-KEM: encapsulation with `H(ek)` given, on every target

**Trusted** (as every file in `Spec/`). `ML-KEM.Encaps_internal(ek, m)`
(FIPS 203 Algorithm 17) starts by hashing the encapsulation key, `H(ek)`
(SHA3-256 of 1184 or 1568 bytes), which depends on the key alone. An
encapsulation key that is used more than once can keep its hash, as the
decapsulation key does (`dk` holds `H(ek)`, §7.1): `vg_mlkem768_encaps_h` and
`vg_mlkem1024_encaps_h` are `vg_mlkem768_encaps` and `vg_mlkem1024_encaps`
with the 32 bytes `h` given, which must be `H(ek)` (the precondition of
`encapsHContract`), and the same postcondition: the outputs of
`ML-KEM.Encaps_internal(ek, m)`, which computes `H(ek)` itself. So an
implementation may use `h` in place of `H(ek)`, and nothing else changes:
the same outcome (`Outcome`), the same leak (`ρ`, and nothing else; `h` is
secret as the rest of `ek` is), the same working space, left with each byte
unchanged or zero.

The caller computes `h` from `ek` once, with SHA3-256 (or takes it from the
decapsulation key, where `vg_mlkem*_keygen` writes it), and passes it with
`ek` to each encapsulation.
-/

@[expose] public section

namespace VG.Spec.MlKem

open Sha3 (bytesAt)

/-- `vg_mlkem*_encaps_h`'s signature, for an encapsulation key of `ekLen`
bytes, a ciphertext of `ctLen` bytes and `scratchWords` words of working
space: `encaps`'s with `h` after `ek`. -/
def encapsHSigOf (ekLen ctLen scratchWords : Nat) : Sig where
  params := [("ek", .array false .u8 ekLen), ("h", .array false .u8 32), ("m", .array false .u8 32),
    ("key", .array true .u8 32), ("ct", .array true .u8 ctLen), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- `vg_mlkem768_encaps_h(ek: *const [u8; 1184], h: *const [u8; 32], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; 1088], scratch: *mut [u64; 4096]) -> u32`. -/
def encapsHSig : Sig := encapsHSigOf 1184 1088 4096

/-- `encapsContract` with the 32 bytes at `h` given, which must be
`H(ek)`: with the encapsulation key at `ek`, its hash at `h` and the 32
bytes of randomness at `m`, writes the shared secret key and the ciphertext
of `ML-KEM.Encaps_internal(ek, m)` (Algorithm 17) of ML-KEM-768 to `key` and
`ct`, and returns 1; or returns 0 (see `Outcome`); and leaves each byte of
`scratch` unchanged or zero. May leak `ρ`, the seed of `Â` in `ek`. -/
def encapsHContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = H (bytesAt m ek 1184))
    (post := fun ek _h msg key ct scratch m m' r =>
      Outcome (fun iters => encapsInternal mlKem768 iters (bytesAt m ek 1184) (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1088) ∧
      Zeroize.scrubbed m m' scratch 32768)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m => leakRho (ekRho mlKem768 (bytesAt m ek 1184)))

/-- `vg_mlkem*_encaps_h` of the parameter set `p` on every target, with the
signature `sig` and the contracts `contracts`, `encapsHContract` of the
namespace `ns`. -/
def Params.encapsHApi (p : Params) (ns : String) (sig : Sig) (contracts : Contracts) : Api where
  module := p.module
  name := p.fn "encaps_h"
  sig := sig
  writeArgs := true
  contracts := some contracts
  summary := s!"{p.name} encapsulation with given randomness and the hash of the key, \
    `ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17): with the encapsulation key `*ek`, \
    its hash `H(ek)` in `*h` and the randomness `*m`, writes the shared secret key to `*key` and \
    the ciphertext to `*ct`, as `{p.fn "encaps"}` does, using `*h` instead of hashing `*ek`. " ++
    outcomeDoc ++ s!"\n\n\
    Contract: `{ns}.encapsHContract`. Constant time but for `ρ`: timing may depend on the \
    pointers and on `ρ` (the last 32 bytes of `*ek`), but not on anything else of the key, on \
    its hash, on the randomness or on the outputs."
  safety := [
    s!"`ek` must have passed `{p.fn "check_ek"}` (FIPS 203 §7.2).",
    "`h` must hold `H(ek)`, the SHA3-256 hash of the bytes of `*ek` (FIPS 203 §4.1).",
    "`m` must be fresh random bytes from an approved RBG (FIPS 203 §3.3).",
    scratchSafetyDoc]

/-- `vg_mlkem768_encaps_h` on every target. -/
def encapsHApi : Api :=
  mlKem768.encapsHApi "VG.Spec.MlKem" encapsHSig fun A stack => encapsHContract A stack

end VG.Spec.MlKem

namespace VG.Spec.MlKem1024

open VG.Spec.MlKem
open Sha3 (bytesAt)

/-- `vg_mlkem1024_encaps_h(ek: *const [u8; 1568], h: *const [u8; 32], m: *const [u8; 32], key: *mut [u8; 32], ct: *mut [u8; 1568], scratch: *mut [u64; 6144]) -> u32`. -/
def encapsHSig : Sig := encapsHSigOf 1568 1568 6144

/-- `VG.Spec.MlKem.encapsHContract` for ML-KEM-1024: `encapsContract` with
the 32 bytes at `h` given, which must be `H(ek)`. -/
def encapsHContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = H (bytesAt m ek 1568))
    (post := fun ek _h msg key ct scratch m m' r =>
      Outcome (fun iters => encapsInternal mlKem1024 iters (bytesAt m ek 1568) (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1568) ∧
      Zeroize.scrubbed m m' scratch 49152)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m => leakRho (ekRho mlKem1024 (bytesAt m ek 1568)))

/-- `vg_mlkem1024_encaps_h` on every target. -/
def encapsHApi : Api :=
  mlKem1024.encapsHApi "VG.Spec.MlKem1024" encapsHSig fun A stack => encapsHContract A stack

end VG.Spec.MlKem1024
