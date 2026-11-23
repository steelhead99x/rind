module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.P384

/-!
# P-384 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-384
(`Spec/P384.lean`): `vg_ec_p384_public_key`, in the module `ec_p384`.
-/

@[expose] public section

namespace VG.Spec.EcKey.P384

/-- P-384. -/
def inst : Instance where
  curve := Spec.P384.curve
  name := "p384"
  title := "P-384"

/-- `vg_ec_p384_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.P384
