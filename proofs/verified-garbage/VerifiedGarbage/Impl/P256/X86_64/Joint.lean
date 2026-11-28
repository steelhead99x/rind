module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
public import VerifiedGarbage.Impl.P256.GTable9

/-! The measured x86-64 P-256 joint multiplication layout and doubling dispatch. -/

@[expose] public section

namespace VG.Impl.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

/-- The verifier's table of `[m]G`, `m = 1 … 256`, which its generator digits
of width nine index, in the static `VG_P256_GTAB`. -/
def p256GTab : CombData :=
  { w := 9, tbl := Impl.P256.p256G9, start := Impl.P256.p256G9Start, tsym := "VG_P256_GTAB" }

/-- P-256 for verification: `p256` with the table of its generator digits
(`gtab`) and without the comb, which only signing and key generation run. -/
def p256v : Cfg := { p256 with comb := none, gtab := some p256GTab }

/-- `p256v` multiplying with BMI2 and ADX. -/
def p256vx : Cfg := { p256x with comb := none, gtab := some p256GTab }

/-- The top digit peeled: its first iteration in the loop measured 0.25%
slower on an Intel Xeon 8370C. The table of `Q`'s odd multiples by co-Z
arithmetic (`coZ`): verification 1.6% faster on an Intel Xeon (Ice Lake). The
generator's digits of width nine (`gw`), in sixteen bits each at `6000`, from
the table `p256GTab`. -/
def publicJoint : Joint.Cfg :=
  { K := p256v.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP,
    gBits := 6000, tsym := "VG_P256_GTAB", cache := 4000, selected := 5408, peel := true,
    coZ := true, gw := 9 }

/-- `publicJoint` with BMI2 and ADX, and the scalars' digits made without branches on their bits
(`recodeB`). -/
def publicJointAdx : Joint.Cfg :=
  { publicJoint with
    K := p256vx.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP
    recodeB := true }

/-- The joint loop's doubler: in place, with a modular halving. -/
def jointDouble (K : WinCfg) : Prog isa := doubleHalfPublic K.M K.S K.R

end VG.Impl.P256.X86_64
