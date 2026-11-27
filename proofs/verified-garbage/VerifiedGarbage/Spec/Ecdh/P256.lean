module

public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Spec.EcKey.P256

/-!
# ECDH over P-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdh_p256`, in the module
`ecdh_p256`, for P-256's `EcKey.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdh.P256

/-- `vg_ecdh_p256` on every target. -/
def exchangeApi : Api := Instance.exchangeApi EcKey.P256.inst

end VG.Spec.Ecdh.P256
