module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.P256

/-!
# P-256 keys: the contracts, on every target

**Trusted** (as every file in `Spec/`). The `Instance` of P-256
(`Spec/P256.lean`): `vg_ec_p256_public_key`, in the module `ec_p256`.
-/

@[expose] public section

namespace VG.Spec.EcKey.P256

/-- P-256. -/
def inst : Instance where
  curve := Spec.P256.curve
  name := "p256"
  title := "P-256"

/-- `vg_ec_p256_public_key` on every target. -/
def publicKeyApi : Api := inst.publicKeyApi

end VG.Spec.EcKey.P256
