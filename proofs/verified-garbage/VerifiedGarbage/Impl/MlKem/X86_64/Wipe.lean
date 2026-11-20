module

public import VerifiedGarbage.Impl.CallWipe.X86_64
public import VerifiedGarbage.Impl.MlKem.X86_64.KeyGenH16
public import VerifiedGarbage.Impl.MlKem.X86_64.EncapsHP16
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem

/-!
# ML-KEM on x86-64: the functions that wipe their working space

Each function of ML-KEM-768 and ML-KEM-1024 taking `scratch` calls its code
(`keyGen`, …), named for the function and `sfx` (the suffix of the
implementation of `vg_mlkem_sample_ntt4` it calls), then the zeroize function
`zname`, whose code is `zcode`, on the bytes of `scratch` that code may write
(`callWipe`): all of it, but with 16-bit polynomials, with which ML-KEM-1024's
writes only its first 37376 bytes.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64 VG.Impl.CallWipe.X86_64 VG.Impl.MlKem1024.X86_64

/-- The bytes of ML-KEM-1024's `scratch` that key generation and
encapsulation with `H(ek)` given write with the implementation `c`. -/
def wiped1024 (c : Callee4) : Nat := if c.s16.isSome then 37376 else 49152

/-- The bytes of ML-KEM-1024's `scratch` that encapsulation hashing the key
and decapsulation write with the implementation `c`. -/
def wipedEnc1024 (c : Callee4) : Nat := if c.s16.isSome && c.batchH16.isSome then 37376 else 49152

/-- `vg_mlkem768_keygen`. -/
def keyGenW (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .rcx 32768 ("vg_mlkem768_keygen_body" ++ sfx) (keyGen c) zname zcode

/-- `vg_mlkem768_encaps_h`. -/
def encapsHW (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .r9 32768 ("vg_mlkem768_encaps_h_body" ++ sfx) (encapsH c) zname zcode

/-- `vg_mlkem768_encaps`. -/
def encapsW (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .r8 32768 ("vg_mlkem768_encaps_body" ++ sfx) (encaps c) zname zcode

/-- `vg_mlkem768_decaps`. -/
def decapsW (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .rcx 32768 ("vg_mlkem768_decaps_body" ++ sfx) (decaps c) zname zcode

/-- `vg_mlkem1024_keygen`. -/
def keyGen1024W (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .rcx (wiped1024 c) ("vg_mlkem1024_keygen_body" ++ sfx) (keyGen1024 c) zname zcode

/-- `vg_mlkem1024_encaps_h`. -/
def encapsH1024W (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .r9 (wiped1024 c) ("vg_mlkem1024_encaps_h_body" ++ sfx) (encapsH1024 c) zname zcode

/-- `vg_mlkem1024_encaps`. -/
def encaps1024W (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .r8 (wipedEnc1024 c) ("vg_mlkem1024_encaps_body" ++ sfx) (encaps1024 c) zname zcode

/-- `vg_mlkem1024_decaps`. -/
def decaps1024W (c : Callee4) (sfx zname : String) (zcode : Prog isa) : Prog isa :=
  callWipe .rcx (wipedEnc1024 c) ("vg_mlkem1024_decaps_body" ++ sfx) (decaps1024 c) zname zcode

end VG.Impl.MlKem.X86_64
