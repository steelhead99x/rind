module

public import VerifiedGarbage.Impl.Ecdh.P256.X86_64
public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Ecdh

/-! # ECDH over P-256 on x86-64 with AVX512_IFMA: `vg_ecdh_p256_adx` with the odd window method's
loop in vectors (`Impl/P256/X86_64/Ifma/Ecdh.lean`) -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `Cfg.mulQJO` for P-256, with the loop in vectors. -/
def mulQP256Ifma : Prog isa :=
  .seq (.block (Cfg.maskK Impl.Ecdsa.X86_64.p256x)) <| .seq (Cfg.jwinPrepO Impl.Ecdsa.X86_64.p256x) <|
  .seq (Impl.P256.X86_64.Ifma.vwindowO (Cfg.jwinCfgO Impl.Ecdsa.X86_64.p256x))
    (.block (Cfg.fixSign Impl.Ecdsa.X86_64.p256x))

/-- `vg_ecdh_p256_ifma`. -/
def exchangeP256Ifma : Prog isa := Cfg.exchangeWith Impl.Ecdsa.X86_64.p256x mulQP256Ifma

end VG.Impl.Ecdh.X86_64
