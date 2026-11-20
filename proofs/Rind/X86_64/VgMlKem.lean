import Rind.X86_64.Funs
import Rind.VgOutcome
open Aeneas Aeneas.Std Result VG.Spec.MlKem

/-!
# pyca/verified-garbage's ML-KEM-768 contracts on x86_64

Each axiom restates the contract in VG's `Spec/MlKem/Contract.lean` (or
`Spec/MlKem/EncapsH.lean`) that VG's theorems prove of the routines one of
rind's wrappers in `low::x86_64::mlkem768_vg` calls, at the revision
`admin/import-vg` pins (0aa40d6c). The wrappers call VG's routines through
raw pointers to a scratch buffer, which Aeneas cannot translate, so each axiom
is about the opaque wrapper, and covers every routine it may call, which all
state the one contract. Their preconditions on memory hold for every call
from safe Rust: each array a routine writes is the wrapper's own, which
overlaps no other argument nor the stack, and the arrays it only reads, which
may alias one another, overlap neither. The CPU features are the wrapper's
to prove: its `KeyPair` token for key generation and decapsulation, and the
check it runs for the variant it picks otherwise, `Width` for encapsulation. What safe Rust cannot show, such as
that a given `h` is `H(ek)`, is the axiom's hypothesis. The postcondition is VG's `Outcome` over the wrapper's arrays as
VG's specs read them, `vgBytes`. VG's wipe of its scratch, which rind keeps
as `AGENTS.md` allows, and what each routine may leak, are left out.

Trusted: the restatement; that rind's `vg_*` routines are VG's at the pin,
whose instructions and relocation targets `admin/prove vg` checks along with
VG's models of the instructions they run; that the constant tables
`admin/import-vg` generates beside them are VG's at the pin, which
`admin/prove vg` checks for each table a routine reaches, byte for byte and
relocation for relocation; and VG's proofs and models.
-/

namespace rind.x86_64

/-- `vg_mlkem768_check_ek`'s and `vg_mlkem768_check_ek_avx2`'s
`checkEkContract`, whose 1 the wrapper returns as `true`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CheckEk.lean#L209 (`checkEk_verified`) and
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CheckEkAvx2.lean#L297 (`checkEkAvx2_verified`). -/
@[step]
axiom vg_mlkem768_check_ek_spec (self : low.x86_64.mlkem768_vg.Encaps)
    (ek : Std.Array U8 1184#usize) :
    low.x86_64.mlkem768_vg.Encaps.check_ek self ek ⦃ b =>
      b = ekCheck mlKem768 (vgBytes ek) ⦄

/-- `vg_mlkem768_encaps`'s `encapsContract` and, where the wrapper is given
`h`, which must then be `H(ek)`, `vg_mlkem768_encaps_h`'s
`encapsHContract`, each with its AVX, AVX2, and AVX-512 variants,
`vg_mlkem768_encaps_avx`, `vg_mlkem768_encaps_avx2`,
`vg_mlkem768_encaps_avx512`, `vg_mlkem768_encaps_h_avx`,
`vg_mlkem768_encaps_h_avx2`, and `vg_mlkem768_encaps_h_avx512`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L750 (`encapsW_verified`) and
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L700 (`encapsHW_verified`). Both hold
for any `ek`.
The wrapper's callers must still check `ek` first, as `Encaps::encaps`
asks; this axiom neither assumes nor establishes that. A proof of the
caller discharges it from `check_ek`'s axiom for a key it imports, and from
the encoding for one it generated. -/
@[step]
axiom vg_mlkem768_encaps_spec (self : low.x86_64.mlkem768_vg.Encaps)
    (ek : Std.Array U8 1184#usize) (h : Option (Std.Array U8 32#usize))
    (m : Std.Array U8 32#usize)
    (hh : ∀ h', h = some h' → vgBytes h' = H (vgBytes ek)) :
    low.x86_64.mlkem768_vg.Encaps.encaps self ek h m ⦃ r =>
      vgOutcome (fun iters => encapsInternal mlKem768 iters (vgBytes ek) (vgBytes m))
        (fun kc => (vgBytes kc.1, vgBytes kc.2)) r ⦄

/-- `vg_mlkem768_keygen_avx512`'s `keyGenContract`, of whose `ek` and `dk`
the wrapper returns `dk`, which holds `ek`:
https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L642 (`keyGenW_verified`). -/
@[step]
axiom vg_mlkem768_keygen_spec (self : low.x86_64.mlkem768_vg.KeyPair)
    (seed : Std.Array U8 64#usize) :
    low.x86_64.mlkem768_vg.KeyPair.keygen self seed ⦃ r =>
      vgOutcome (fun iters => (keyGenInternal mlKem768 iters ((vgBytes seed).take 32)
          ((vgBytes seed).drop 32)).map Prod.snd) vgBytes r ⦄

/-- `vg_mlkem768_decaps_avx512`'s `decapsContract`, which holds for any
`dk`: https://github.com/pyca/verified-garbage/blob/0aa40d6c21fd02943fe5b38a5b69b6213d07764d/lean/VerifiedGarbage/Proof/MlKem/X86_64/CallWipe.lean#L799 (`decapsW_verified`).
The wrapper's callers must still pass a `dk` from `keygen`, as VG's API and
`KeyPair::decaps` ask; this axiom neither assumes nor establishes that. -/
@[step]
axiom vg_mlkem768_decaps_spec (self : low.x86_64.mlkem768_vg.KeyPair)
    (dk : Std.Array U8 2400#usize) (c : Std.Array U8 1088#usize) :
    low.x86_64.mlkem768_vg.KeyPair.decaps self dk c ⦃ r =>
      vgOutcome (fun iters => decapsInternal mlKem768 iters (vgBytes dk) (vgBytes c)) vgBytes r ⦄

end rind.x86_64
