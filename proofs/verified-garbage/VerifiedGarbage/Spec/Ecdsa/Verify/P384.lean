module

public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.P384

/-!
# ECDSA signature verification over P-384: the contracts, on every target

**Trusted** (as every file in `Spec/`). `vg_ecdsa_p384_verify`, in the
module `ecdsa_p384`, for P-384's `Ecdsa.Instance`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa.P384

/-- `vg_ecdsa_p384_verify` on every target, taking the hash function's output. -/
def verifyHashApi : Api := inst.verifyHashApi

end VG.Spec.Ecdsa.P384
