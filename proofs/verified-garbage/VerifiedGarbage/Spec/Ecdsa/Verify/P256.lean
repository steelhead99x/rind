module

public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.P256

/-!
# ECDSA signature verification over P-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_p256_verify`, in the
module `ecdsa_p256`, for P-256's `Ecdsa.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P256

/-- `vg_ecdsa_p256_verify` on every target, taking the hash function's output. -/
def verifyHashApi : Api := inst.verifyHashApi

end VG.Spec.Ecdsa.P256
