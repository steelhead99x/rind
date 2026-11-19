import Rind.Aarch64.Funs
import Rind.VgOutcome
open Aeneas Aeneas.Std Result VG.Spec.MlKem

/-!
# pyca/verified-garbage's ML-KEM-768 contracts on aarch64

As `Rind/X86_64/VgMlKem.lean`, for the wrappers in
`low::aarch64::mlkem768_vg`: the encapsulation key check, and encapsulation
with the SHA-3 instructions, whose token the wrapper holds. Encapsulation runs
VG's variant over the two-state SHA-3 Keccak, with its one-state Keccak on the
SHA-3 instructions on Apple's cores and on NEON elsewhere: the wrapper picks
it by target, as VG's dispatcher would, and calls it directly. Each states the
one contract.
-/

namespace rind.aarch64

/-- `vg_mlkem768_check_ek`'s `checkEkContract`, whose 1 the wrapper returns
as `true`: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/AArch64/Residue.lean#L36
(`checkEk768Cleared_verified`). -/
@[step]
axiom vg_mlkem768_check_ek_spec (self : low.aarch64.mlkem768_vg.Encaps)
    (ek : Std.Array U8 1184#usize) :
    low.aarch64.mlkem768_vg.Encaps.check_ek self ek ⦃ b =>
      b = ekCheck mlKem768 (vgBytes ek) ⦄

/-- `vg_mlkem768_encaps_x2_sha3`'s and
`vg_mlkem768_encaps_x2_sha3_keccak_sha3`'s `encapsContract` and, where the
wrapper is given `h`, which must then be `H(ek)`,
`vg_mlkem768_encaps_h_x2_sha3`'s and
`vg_mlkem768_encaps_h_x2_sha3_keccak_sha3`'s `encapsHContract`: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/AArch64/CallWipe.lean#L1095
(`Wipe.encapsP768_verified`) and
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/AArch64/CallWipe.lean#L1085 (`Wipe.encapsHP768_verified`).
Both hold for any `ek`.
The wrapper's callers must still check `ek` first, as `Encaps::encaps`
asks; this axiom neither assumes nor establishes that. A proof of the
caller discharges it from `check_ek`'s axiom for a key it imports, and from
the encoding for one it generated. -/
@[step]
axiom vg_mlkem768_encaps_spec (self : low.aarch64.mlkem768_vg.Encaps)
    (ek : Std.Array U8 1184#usize) (h : Option (Std.Array U8 32#usize))
    (m : Std.Array U8 32#usize)
    (hh : ∀ h', h = some h' → vgBytes h' = H (vgBytes ek)) :
    low.aarch64.mlkem768_vg.Encaps.encaps self ek h m ⦃ r =>
      vgOutcome (fun iters => encapsInternal mlKem768 iters (vgBytes ek) (vgBytes m))
        (fun kc => (vgBytes kc.1, vgBytes kc.2)) r ⦄

end rind.aarch64
