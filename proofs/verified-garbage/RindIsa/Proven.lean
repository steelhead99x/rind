import RindIsa.AArch64.ChaCha20Poly1305
import RindIsa.AArch64.Sha256Hw
import RindIsa.X86_64.ChaCha20Poly1305
import RindIsa.X86_64.Mul4x
import RindIsa.X86_64.GcmInitAvx2
import RindIsa.X86_64.Mulx4x
import RindIsa.X86_64.PolyHashAd
import RindIsa.X86_64.Sqrx8x
import RindIsa.X86_64.Sqrx8xMont

/-! The functions rind proves in its models of AArch64 and x86_64, which
`rind-asm` prints and `vg-cosim --rind` cosimulates. -/

namespace Rind.AArch64

/-- A function rind proves, its body's program, and the statics it reads:
each its symbol in the program, its Rust path, and the words it begins
with. -/
structure Proven where
  path : String
  prog : VG.Prog isa
  statics : List (String × String × List (BitVec 32))

def proven : List Proven :=
  [{ path := "rind::low::aarch64::sha256::sha256_block_data_order_hw", prog := Sha256Hw.prog,
     statics := [(Sha256Hw.kName, "rind::low::aarch64::sha256::K256", Sha256Hw.table)] },
   { path := "rind::low::aarch64::chacha20poly1305::chacha20_poly1305_seal",
     prog := ChaCha20Poly1305.sealProg,
     statics := [(ChaCha20Poly1305.constsName, "rind::low::aarch64::chacha20poly1305::CHACHA20_CONSTS",
       ChaCha20Poly1305.consts)] },
   { path := "rind::low::aarch64::chacha20poly1305::chacha20_poly1305_open",
     prog := ChaCha20Poly1305.openProg,
     statics := [(ChaCha20Poly1305.constsName, "rind::low::aarch64::chacha20poly1305::CHACHA20_CONSTS",
       ChaCha20Poly1305.consts)] }]

end Rind.AArch64

namespace Rind.X86_64

/-- A function rind proves in its model of x86_64, its body's program, its
return's bytes (`repRet` or `plainRet`), and the statics it reads: each its
name in the program, its Rust path, and the words it begins with. -/
structure Proven where
  path : String
  prog : VG.Prog isa
  ret : List Nat
  statics : List (String × String × List (BitVec 64))

def proven : List Proven :=
  [{ path := "rind::low::x86_64::mont::bn_mul4x_mont", prog := Mul4x.prog, ret := repRet, statics := [] },
   { path := "rind::low::x86_64::mont::bn_mulx4x_mont", prog := Mulx4x.prog, ret := repRet, statics := [] },
   { path := "rind::low::x86_64::chacha20poly1305::poly_hash_ad_internal", prog := PolyHashAd.prog, ret := repRet,
     statics := [] },
   { path := "rind::low::x86_64::aes_gcm_vaes::gcm_init_vpclmulqdq_avx2", prog := GcmInitAvx2.prog,
     ret := plainRet,
     statics := [(GcmInitAvx2.carryName, "rind::low::x86_64::aes_gcm_vaes::AVX2_GFPOLY_AND_INTERNAL_CARRYBIT",
         GcmInitAvx2.carry),
       (GcmInitAvx2.gfpolyName, "rind::low::x86_64::aes_gcm_vaes::AVX2_GFPOLY", GcmInitAvx2.gfpoly)] },
   { path := "rind::low::x86_64::chacha20poly1305::seal_avx2", prog := ChaCha20Poly1305.sealAvx2,
     ret := repRet,
     statics := [(ChaCha20Poly1305.constsName, "rind::low::x86_64::chacha20poly1305::CONSTS",
       ChaCha20Poly1305.consts)] },
   { path := "rind::low::x86_64::mont::bn_sqrx8x_internal", prog := Sqrx8x.prog, ret := repRet, statics := [] },
   { path := "rind::low::x86_64::mont::bn_sqrx8x_mont", prog := Sqrx8xMont.prog, ret := repRet, statics := [] }]

end Rind.X86_64
