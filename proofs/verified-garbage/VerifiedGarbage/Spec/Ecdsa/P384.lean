module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.P384

/-!
# ECDSA over P-384: its instance

**Trusted** (as every file in `Spec/`). The `Instance` of P-384
(`Spec/P384.lean`), for the functions of the module `ecdsa_p384`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P384

/-- P-384. -/
def inst : Instance where
  curve := Spec.P384.curve
  name := "p384"
  title := "P-384"

end VG.Spec.Ecdsa.P384
