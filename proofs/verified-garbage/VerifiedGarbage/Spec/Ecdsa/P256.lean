module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.P256

/-!
# ECDSA over P-256: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of P-256
(`Spec/P256.lean`), for the functions of the module `ecdsa_p256`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P256

/-- P-256. -/
def inst : Instance where
  curve := Spec.P256.curve
  name := "p256"
  title := "P-256"

end VG.Spec.Ecdsa.P256
