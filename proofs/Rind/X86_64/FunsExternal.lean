module
public import Aeneas
public import Rind.X86_64.Types
public import Rind.X86_64.AesGcmModel
public import Rind.X86_64.PointSelectModel
public import Rind.X86_64.GatherModel
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
The rind functions the x86_64 translation leaves opaque, beside those
`Rind.X86_64.AesGcmModel`, `Rind.X86_64.PointSelectModel`, and
`Rind.X86_64.GatherModel` model, and the eight-way Keccak-f's `set_row`,
which this file models by hand, quoting its Rust. No proof assumes anything about them beyond what
`Rind.X86_64.S2nBignum`, `Rind.X86_64.AwsLc`, `Rind.X86_64.ValeAesGcm`,
`Rind.X86_64.VgRsa`, `Rind.X86_64.VgChaCha20`, and `Rind.X86_64.RsaMont`'s
`nohw_spec` state for s2n-bignum's, aws-lc's, Vale's, and
pyca/verified-garbage's routines, what
`Rind.X86_64.CtEqual` states for the constant-time compares, and what each theorem
takes as a hypothesis.
-/

namespace rind.x86_64

/-! s2n-bignum's routines, transliterated to inline assembly. -/

opaque low.x86_64.curve25519_x25519base_alt.curve25519_x25519base_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.x86_64.curve25519_x25519base.curve25519_x25519base
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.x86_64.sha3_keccak_f1600.sha3_keccak_f1600
  : Array Std.U64 25#usize → Array Std.U64 24#usize → Result (Array Std.U64 25#usize)

opaque low.x86_64.sha3_keccak4_f1600_alt.sha3_keccak4_f1600
  : Array (Array Std.U64 25#usize) 4#usize → Array Std.U64 24#usize → Array Std.U64 4#usize →
    Array Std.U64 4#usize → Result (Array (Array Std.U64 25#usize) 4#usize)

opaque low.x86_64.bignum_eq.bignum_eq
  : Slice Std.U64 → Slice Std.U64 → Result Bool

opaque low.x86_64.curve25519_x25519_alt.curve25519_x25519_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.x86_64.curve25519_x25519.curve25519_x25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

/-! OpenSSL's and aws-lc's SHA-512 routines, behind their Rust wrappers. -/

opaque low.x86_64.sha512.compress_avx2
  :
  low.x86_64.cpu.HaveAvx2 → Array Std.U64 8#usize → Slice Std.U8 → Result
    (Array Std.U64 8#usize)

opaque low.x86_64.sha512.compress_avx
  :
  low.x86_64.cpu.HaveAvx → Array Std.U64 8#usize → Slice Std.U8 → Result
    (Array Std.U64 8#usize)

opaque low.x86_64.sha512.compress_nohw
  : Array Std.U64 8#usize → Slice Std.U8 → Result (Array Std.U64 8#usize)

/-! Vale's AES-GCM routines, behind their Rust wrappers. -/

opaque low.x86_64.aes_gcm_avx.counter_block
  :
  Std.Array Std.U8 12#usize → Std.Array Std.U8 16#usize →
    Std.Array core.core_arch.x86.__m128i 8#usize → low.x86_64.cpu.HaveAvxMovbeForAesGcm →
    Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.aes_gcm_avx.aead
  (ENC : Bool) :
  low.x86_64.aes.HwKey → Std.Array core.core_arch.x86.__m128i 8#usize →
    low.x86_64.aes_gcm_avx.Buffers → low.x86_64.cpu.HaveAvxMovbeForAesGcm →
    Result (Std.U64 × low.x86_64.aes_gcm_avx.Buffers)

/-! The constant-time compares behind `low::generic::ct_equal`, whose inline
assembly `Rind.X86_64.CtEqual` states HOL Light's theorems about. -/

opaque low.x86_64.cpu.ct_compare_16
  : Array Std.U8 16#usize → Array Std.U8 16#usize → Result Std.Usize

opaque low.x86_64.cpu.ct_compare_bytes : Slice Std.U8 → Slice Std.U8 → Result Std.U8

opaque low.x86_64.vpaes_x86_64.VpaesKey.new
  : Slice Std.U8 → low.x86_64.cpu.HaveSsse3 → Result low.x86_64.vpaes_x86_64.VpaesKey

opaque low.x86_64.vpaes_x86_64.VpaesKey.encrypt_block
  : low.x86_64.vpaes_x86_64.VpaesKey → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.vpaes_x86_64.VpaesDecKey.new
  : Slice Std.U8 → low.x86_64.cpu.HaveSsse3 → Result low.x86_64.vpaes_x86_64.VpaesDecKey

opaque low.x86_64.vpaes_x86_64.VpaesDecKey.decrypt_block
  : low.x86_64.vpaes_x86_64.VpaesDecKey → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.aes_nohw.NohwKey.new : Slice Std.U8 → Result low.x86_64.aes_nohw.NohwKey

opaque low.x86_64.aes_nohw.NohwKey.decrypt_block
  : low.x86_64.aes_nohw.NohwKey → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.aes_nohw.NohwKey.encrypt_block
  : low.x86_64.aes_nohw.NohwKey → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)

opaque low.x86_64.aes_nohw.NohwKey.ctr32
  : low.x86_64.aes_nohw.NohwKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

opaque low.x86_64.aes_nohw.NohwKey.cbc_encrypt
  : low.x86_64.aes_nohw.NohwKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

opaque low.x86_64.aes_nohw.NohwKey.cbc_decrypt
  : low.x86_64.aes_nohw.NohwKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

opaque low.x86_64.vpaes_x86_64.VpaesKey.ctr32
  : low.x86_64.vpaes_x86_64.VpaesKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

opaque low.x86_64.vpaes_x86_64.VpaesKey.cbc_encrypt
  : low.x86_64.vpaes_x86_64.VpaesKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

opaque low.x86_64.vpaes_x86_64.VpaesDecKey.cbc_decrypt
  : low.x86_64.vpaes_x86_64.VpaesDecKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

/-- aws-lc's AES-NI CTR32 routine on whole blocks; `Rind.X86_64.AesModesLow`
assumes its pending HOL Light theorem. -/
opaque low.x86_64.aes_ctr.hw_ctr32
  : low.x86_64.aes.HwKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

/-- aws-lc's AES-NI CBC routine, encrypting; `Rind.X86_64.AesModesLow` restates
its HOL Light theorem. -/
opaque low.x86_64.aes_cbc.hw_encrypt
  : low.x86_64.aes.HwKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

/-- aws-lc's AES-NI CBC routine, decrypting; `Rind.X86_64.AesModesLow` assumes
its pending HOL Light theorem. -/
opaque low.x86_64.aes_cbc.hw_decrypt
  : low.x86_64.aes.HwDecKey → Std.Array Std.U8 16#usize → Slice (Std.Array Std.U8 16#usize) →
    Result (Slice (Std.Array Std.U8 16#usize))

opaque low.x86_64.ghash_ssse3_x86_64.Ssse3Table.new
  : Std.Array Std.U8 16#usize → low.x86_64.cpu.HaveSsse3 → Result low.x86_64.ghash_ssse3_x86_64.Ssse3Table

opaque low.x86_64.ghash_nohw.NohwTable.new
  : Std.Array Std.U8 16#usize → Result low.x86_64.ghash_nohw.NohwTable

opaque low.x86_64.ghash.ClmulTable.from_powers
  : Slice core.core_arch.x86.__m128i → low.x86_64.cpu.HaveAesHardware → Result low.x86_64.ghash.ClmulTable

opaque low.x86_64.aes_gcm_vaes.VaesKernel.avx512
  : Std.U128 → low.x86_64.cpu.HaveAvx512ForAesGcm → Result low.x86_64.aes_gcm_vaes.VaesKernel

opaque low.x86_64.aes_gcm_vaes.VaesKernel.avx2
  : Std.U128 → low.x86_64.cpu.HaveVaesAvx2ForAesGcm → Result low.x86_64.aes_gcm_vaes.VaesKernel

/-- The empty cell for VG's AES-GCM context, on the CPUs that run it. -/
opaque low.x86_64.aes_gcm_vg.LazyVgKey.new
  : low.x86_64.cpu.HaveAvx512ForAesGcm → Result (Option low.x86_64.aes_gcm_vg.LazyVgKey)

/-- Wiping and freeing VG's AES-GCM context, which no proof observes. -/
opaque low.x86_64.aes_gcm_vg.LazyVgKey.wipe
  : low.x86_64.aes_gcm_vg.LazyVgKey → Result low.x86_64.aes_gcm_vg.LazyVgKey

opaque low.x86_64.aes_gcm_vg.LazyVgKey.get
  : low.x86_64.aes_gcm_vg.LazyVgKey → low.x86_64.aes.HwKey → Result low.x86_64.aes_gcm_vg.VgKey

opaque low.x86_64.aes_gcm_vg.VgKey.seal
  : low.x86_64.aes_gcm_vg.VgKey → Std.Array U8 12#usize → Slice U8 → Slice U8 →
    Result ((Std.Array U8 16#usize) × (Slice U8))

opaque low.x86_64.aes_gcm_vg.VgKey.open
  : low.x86_64.aes_gcm_vg.VgKey → Std.Array U8 12#usize → Slice U8 → Slice U8 →
    Std.Array U8 16#usize → Result (Bool × (Slice U8))

/-- Wiping a value, which no proof observes: the translation ignores drops. -/
opaque low.generic.zeroise.zeroise_value {T : Type} (ZeroableInst : low.generic.zeroise.Zeroable T) :
  T → Result T

/-! ChaCha20-Poly1305's routines: pyca/verified-garbage's AVX-512 IFMA seal
and open, behind one wrapper each, whose contracts
`Rind.X86_64.VgChaCha20Poly1305` restates; aws-lc's
one-pass seal and open, behind their Rust wrapper, whose contract
`Rind.X86_64.ChaCha20Poly1305`'s `OnePass` states as a hypothesis; and the
separate passes CPUs without SSE4.1 run, which no theorem is about. -/

opaque low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305.check_seal
  : Std.Usize → Result (Option low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305)

opaque low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305.check_open
  : Std.Usize → Result (Option low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305)

opaque low.x86_64.chacha20poly1305.seal_ifma
  : low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305 → Std.Array Std.U8 32#usize →
    Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 →
    Result ((Std.Array Std.U8 16#usize) × (Slice Std.U8))

opaque low.x86_64.chacha20poly1305.open_ifma
  : low.x86_64.cpu.HaveIfmaForVgChaCha20Poly1305 → Std.Array Std.U8 32#usize →
    Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 → Std.Array Std.U8 16#usize →
    Result (Bool × (Slice Std.U8))

opaque low.x86_64.chacha20poly1305.one_pass
  : low.x86_64.cpu.HaveSse41 → Option low.x86_64.cpu.HaveAvx2 → Std.Array Std.U8 32#usize →
    Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 → Bool →
    Result ((Std.Array Std.U8 16#usize) × (Slice Std.U8))

opaque low.generic.chacha20poly1305.seal
  : Std.Array Std.U8 32#usize → Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 →
    Result ((Std.Array Std.U8 16#usize) × (Slice Std.U8))

opaque low.generic.chacha20poly1305.open
  : Std.Array Std.U8 32#usize → Std.Array Std.U8 12#usize → Slice Std.U8 → Slice Std.U8 →
    Std.Array Std.U8 16#usize → Result (Bool × (Slice Std.U8))

/-! `cipher::ChaCha20`'s routines: pyca/verified-garbage's, behind one
wrapper each, whose contracts `Rind.X86_64.VgChaCha20` restates, and aws-lc's
SSSE3 routine, whose HOL Light theorem `Rind.X86_64.ChaCha20Cipher`
restates. -/

opaque low.x86_64.cpu.HaveAvx512Vl.check : Result (Option low.x86_64.cpu.HaveAvx512Vl)

opaque low.x86_64.chacha20.VgState.uninit : Result low.x86_64.chacha20.VgState

opaque low.x86_64.chacha20.VgState.init
  : low.x86_64.chacha20.VgState → Std.Array Std.U32 8#usize → Std.Array Std.U32 4#usize →
    Result low.x86_64.chacha20.VgState

opaque low.x86_64.chacha20.VgState.apply_avx2
  : low.x86_64.chacha20.VgState → low.x86_64.cpu.HaveAvx2 → Slice Std.U8 →
    Result (Std.U32 × low.x86_64.chacha20.VgState × (Slice Std.U8))

opaque low.x86_64.chacha20.VgState.apply_avx512vl
  : low.x86_64.chacha20.VgState → low.x86_64.cpu.HaveAvx512Vl → Slice Std.U8 →
    Result (Std.U32 × low.x86_64.chacha20.VgState × (Slice Std.U8))

opaque low.x86_64.chacha20.cipher_ssse3_4x
  : low.x86_64.cpu.HaveSsse3 → Std.Array Std.U32 8#usize → Std.Array Std.U32 4#usize →
    Slice Std.U8 → Result (Slice Std.U8)

/-! The eight-way AVX-512 Keccak-f's store of one vector to a state's lanes,
which goes through a raw pointer, modelled by hand. `admin/prove` fails unless
this quote is still that Rust:

```rust
fn set_row(s: &mut [u64; 25], i: usize, v: __m512i) {
    // SAFETY: the eight lanes are 64 bytes, exactly the width of one `__m512i`.
    unsafe { _mm512_storeu_si512(s[i..i + 8].as_mut_ptr().cast(), v) }
}

```

The slice `s[i..i + 8]` panics unless `i + 8 ≤ 25`, and an unaligned store
writes `v`'s 64-bit elements to it in order, element 0 first. -/

/-- `set_row`: lanes `i` to `i + 7` of `s` replaced by `v`'s elements. -/
def low.x86_64.sha3_keccak8_f1600.set_row (s : Array Std.U64 25#usize) (i : Std.Usize)
    (v : core.core_arch.x86.__m512i) : Result (Array Std.U64 25#usize) :=
  if h : i.val + 8 ≤ 25 then
    ok (Array.make 25#usize (s.val.take i.val ++ (List.range 8).map (fun k => ⟨rind.simd.lane64x8 v k⟩) ++
      s.val.drop (i.val + 8)) (by simp; omega))
  else fail .panic

/-! s2n-bignum's Ed25519 routines, transliterated to inline assembly. -/

opaque low.x86_64.edwards25519_decode.edwards25519_decode
  :
  Array Std.U64 8#usize → Array Std.U8 32#usize → Result (Bool × (Array
    Std.U64 8#usize))

opaque low.x86_64.edwards25519_scalarmulbase.edwards25519_scalarmulbase
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Result (Array Std.U64
    8#usize)

opaque low.x86_64.bignum_madd_n25519.bignum_madd_n25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.edwards25519_decode_alt.edwards25519_decode_alt
  :
  Array Std.U64 8#usize → Array Std.U8 32#usize → Result (Bool × (Array
    Std.U64 8#usize))

opaque low.x86_64.edwards25519_scalarmulbase_alt.edwards25519_scalarmulbase_alt
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Result (Array Std.U64
    8#usize)

opaque low.x86_64.bignum_madd_n25519_alt.bignum_madd_n25519_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_mod_n25519.bignum_mod_n25519
  : Array Std.U64 4#usize → Slice Std.U64 → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_neg_p25519.bignum_neg_p25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64
    4#usize)

opaque low.x86_64.bignum_cmp_lt.bignum_cmp_lt
  : Slice Std.U64 → Slice Std.U64 → Result Std.U64

opaque low.x86_64.bignum_mul_p25519.bignum_mul_p25519
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_mul_p25519_alt.bignum_mul_p25519_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

/-! s2n-bignum's Edwards point routines, which Ed25519 verification's
multi-scalar multiplication runs, and that multiplication's AVX2 port, which
no proof covers yet (`quest/m4/verified/ed25519-avx2-verify.md`). -/

opaque low.x86_64.edwards25519_epadd.edwards25519_epadd
  :
  Array Std.U64 16#usize → Array Std.U64 16#usize → Array Std.U64 16#usize
    → Result (Array Std.U64 16#usize)

opaque low.x86_64.edwards25519_epadd_alt.edwards25519_epadd_alt
  :
  Array Std.U64 16#usize → Array Std.U64 16#usize → Array Std.U64 16#usize
    → Result (Array Std.U64 16#usize)

opaque low.x86_64.edwards25519_epdouble.edwards25519_epdouble
  :
  Array Std.U64 16#usize → Array Std.U64 12#usize → Result (Array Std.U64
    16#usize)

opaque low.x86_64.edwards25519_epdouble_alt.edwards25519_epdouble_alt
  :
  Array Std.U64 16#usize → Array Std.U64 12#usize → Result (Array Std.U64
    16#usize)

opaque low.x86_64.edwards25519_pdouble.edwards25519_pdouble
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Result (Array Std.U64
    12#usize)

opaque low.x86_64.edwards25519_pdouble_alt.edwards25519_pdouble_alt
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Result (Array Std.U64
    12#usize)

opaque low.x86_64.edwards25519_msm_avx2.edwards25519_msm
  :
  Array Std.U64 12#usize → Array Std.U64 4#usize → Array (Array Std.U64
    4#usize) 2#usize → Array (Array Std.U64 16#usize) 2#usize →
    low.x86_64.cpu.HaveAvx2 → Result (Array Std.U64 12#usize)

/-! The wipe, which writes zeros over a slice through raw pointers, which Aeneas
cannot translate, so this models it: it returns, leaving the zeros `wiped`
stands for. `admin/prove` fails unless this quote is still that Rust:

```rust
pub(crate) fn zeroise<T: Zeroable>(v: &mut [T]) {
    // SAFETY: `v` is `size_of_val(v)` writable bytes, and `T: Zeroable`
    // makes all-zero bytes a valid `T`.
    unsafe { zero_bytes(v.as_mut_ptr().cast(), size_of_val(v)) };
}

```
-/

/-- What `zeroise` leaves in `v`: all-bits-zero, which `Zeroable` makes a
valid `T` but cannot name, so it is opaque, its value `v` only witnessing
that it has one. No proof reads a slice after its wipe. -/
opaque low.generic.zeroise.wiped {T : Type _} (v : Slice T) : Slice T := v

/-- `zeroise`, which returns. -/
def low.generic.zeroise.zeroise {T : Type _} (_ZeroableInst : low.generic.zeroise.Zeroable T)
    (v : Slice T) : Result (Slice T) :=
  ok (low.generic.zeroise.wiped v)

/-- `ZeroableRef::new`, as `Rind.X86_64.Dispatch` models a `ZeroableRef`: its
value. -/
def low.generic.zeroise.ZeroableRef.new {T : Type} (value : T) :
    Result (low.generic.zeroise.ZeroableRef T) :=
  ok value

/-! The entry guard and CPU dispatch, which read no input. -/

opaque low.entry.Entry.new_secret : Result low.entry.Entry

opaque low.entry.Entry.new_public : Result low.entry.Entry

/-- Whether an entry guard is held, which a debug build asserts. -/
opaque low.entry.Entry.assert_held : Result Unit

opaque low.x86_64.sha512.path : Result low.x86_64.sha512.Path

opaque low.x86_64.cpu.HaveBmi2Adx.check
  : Result (Option low.x86_64.cpu.HaveBmi2Adx)

opaque low.x86_64.cpu.HaveAvx512ForRsa.check
  : Result (Option low.x86_64.cpu.HaveAvx512ForRsa)

opaque low.x86_64.cpu.HaveAvx512ForRsa.fp16
  : low.x86_64.cpu.HaveAvx512ForRsa → Result Bool

/-- Wiping VG's CRT values, which no proof observes: the translation ignores
drops. -/
opaque low.x86_64.rsa_ifma.IfmaCrt.Insts.CoreOpsDropDrop.drop
  : low.x86_64.rsa_ifma.IfmaCrt → Result low.x86_64.rsa_ifma.IfmaCrt

/-- pyca/verified-garbage's AVX-512 IFMA public operation and CRT, behind
the Rust that sizes their scratch and calls them, which `Rind.X86_64.VgRsa`
states. -/
opaque low.x86_64.rsa_ifma.RsaIfma.public
  : low.x86_64.rsa_ifma.RsaIfma → Slice Std.U8 → Slice Std.U64 → Slice Std.U8 → Slice Std.U8 →
    Result (Bool × Slice Std.U8)

/-- pyca/verified-garbage's RSA `R² mod n`, behind the Rust that sizes its
scratch and calls it, which `Rind.X86_64.VgRsa` states. -/
opaque low.x86_64.rsa_vg.Precompute.precompute
  : low.x86_64.rsa_vg.Precompute → Slice Std.U64 → Slice Std.U8 → Result (Bool × Slice Std.U64)

opaque low.x86_64.rsa_ifma.IfmaCrt.crt
  : low.x86_64.rsa_ifma.IfmaCrt → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
    Slice Std.U8 → Result (Bool × Slice Std.U8)

opaque low.x86_64.cpu.HaveAvx2.check : Result (Option low.x86_64.cpu.HaveAvx2)

/-! The table selects, over `Rind.X86_64.PointSelectModel`'s model of
`select_avx2` and `select_sse2`, which quotes them. -/

/-- `bignum_aff_point_select_p256`. -/
def low.x86_64.bignum_point_select.bignum_aff_point_select_p256 (z : Array Std.U64 8#usize)
    (table : Slice Std.U64) (index : Std.U8) : Result (Array Std.U64 8#usize) := do
  let o ← low.x86_64.cpu.HaveAvx2.check
  match o with
  | some token => low.x86_64.bignum_point_select.select_avx2 8#usize 2 z table index token
  | none => low.x86_64.bignum_point_select.select_sse2 8#usize 4 z table index

/-- `bignum_aff_point_select_p384`. -/
def low.x86_64.bignum_point_select.bignum_aff_point_select_p384 (z : Array Std.U64 12#usize)
    (table : Slice Std.U64) (index : Std.U8) : Result (Array Std.U64 12#usize) := do
  let o ← low.x86_64.cpu.HaveAvx2.check
  match o with
  | some token => low.x86_64.bignum_point_select.select_avx2 12#usize 3 z table index token
  | none => low.x86_64.bignum_point_select.select_sse2 12#usize 6 z table index

/-- `bignum_aff_point_select_p521`. -/
def low.x86_64.bignum_point_select.bignum_aff_point_select_p521 (z : Array Std.U64 18#usize)
    (table : Slice Std.U64) (index : Std.U8) : Result (Array Std.U64 18#usize) := do
  let o ← low.x86_64.cpu.HaveAvx2.check
  match o with
  | some token => low.x86_64.bignum_point_select.select_avx2 18#usize 4 z table index token
  | none => low.x86_64.bignum_point_select.select_sse2 18#usize 9 z table index

opaque low.x86_64.cpu.HaveAesHardware.check : Result (Option low.x86_64.cpu.HaveAesHardware)

opaque low.x86_64.cpu.HaveAvxMovbeForAesGcm.check
  : Result (Option low.x86_64.cpu.HaveAvxMovbeForAesGcm)

opaque low.x86_64.cpu.HaveVaesAvx2ForAesGcm.check
  : Result (Option low.x86_64.cpu.HaveVaesAvx2ForAesGcm)

opaque low.x86_64.cpu.HaveAvx512ForAesGcm.check
  : Result (Option low.x86_64.cpu.HaveAvx512ForAesGcm)

opaque low.x86_64.cpu.HaveVaesAvx2ForAesGcm.avx_movbe
  : low.x86_64.cpu.HaveVaesAvx2ForAesGcm → Result low.x86_64.cpu.HaveAvxMovbeForAesGcm

opaque low.x86_64.cpu.HaveSsse3.check : Result (Option low.x86_64.cpu.HaveSsse3)

opaque low.x86_64.cpu.HaveSse41.check : Result (Option low.x86_64.cpu.HaveSse41)

/-- The SHA-1 and SHA-256 routines the CPU runs, each picked once. -/
opaque low.x86_64.sha1_mux.path : Result low.x86_64.sha1_mux.Path

opaque low.x86_64.sha256_mux.path : Result low.x86_64.sha256_mux.Path

/-! SHA-1 and SHA-256's block and finishing functions. `Rind.X86_64.ShaBlocks` states SHA-1's
contracts as hypotheses, and `Rind.X86_64.Sha256Shaext` SHA-256's as axioms restating their
HOL Light proofs. SHA-1's block function is its whole dispatch, which `Sha1Blocks` states as
one. `finish_padded` is `sha256_finish_shaext`'s `asm!` block, below its padding. -/

opaque low.x86_64.sha1_mux.sha1_compress_blocks
  : Array Std.U32 5#usize → Slice Std.U8 → Result (Array Std.U32 5#usize)

opaque low.x86_64.sha1.sha1_compress_padded_shaext
  : Array Std.U32 5#usize → Slice Std.U8 → Array Std.U8 8#usize → low.x86_64.cpu.HaveSha1 →
    Result (Array Std.U32 5#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_shaext
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveSha256 →
    Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.finish_padded
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.sha256.Padded → low.x86_64.cpu.HaveSha256 →
    Result (Array Std.U8 32#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_avx
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveAvx → Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_avx2
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveAvx2 → Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_ssse3
  : Array Std.U32 8#usize → Slice Std.U8 → low.x86_64.cpu.HaveSsse3 →
    Result (Array Std.U32 8#usize)

opaque low.x86_64.sha256.sha256_compress_blocks_nohw
  : Array Std.U32 8#usize → Slice Std.U8 → Result (Array Std.U32 8#usize)

/-! P-384's s2n-bignum routines and `bignum_mux`. -/

opaque low.x86_64.bignum_add_p384.bignum_add_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.x86_64.bignum_demont_p384.bignum_demont_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_demont_p384_alt.bignum_demont_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_inv_p384.bignum_inv_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_montmul_p384.bignum_montmul_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.x86_64.bignum_montmul_p384_alt.bignum_montmul_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Array Std.U64 6#usize →
    Result (Array Std.U64 6#usize)

opaque low.x86_64.bignum_montsqr_p384.bignum_montsqr_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_montsqr_p384_alt.bignum_montsqr_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_mux.bignum_mux
  :
  Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result
    (Slice Std.U64)

opaque low.x86_64.bignum_neg_p384.bignum_neg_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_tomont_p384.bignum_tomont_p384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.bignum_tomont_p384_alt.bignum_tomont_p384_alt
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.p384_montjdouble.p384_montjdouble
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Result (Array Std.U64
    18#usize)

opaque low.x86_64.p384_montjdouble_alt.p384_montjdouble_alt
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Result (Array Std.U64
    18#usize)

opaque low.x86_64.p384_montjmixadd.p384_montjmixadd
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Array Std.U64 12#usize
    → Result (Array Std.U64 18#usize)

opaque low.x86_64.p384_montjmixadd_alt.p384_montjmixadd_alt
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Array Std.U64 12#usize
    → Result (Array Std.U64 18#usize)

/-! Whether the CPU runs pyca/verified-garbage's P-384 `d·G`, for key
generation and ECDSA's nonces, and its ECDSA verification, which read no
input, and its routines behind their Rust wrappers, whose contracts
`Rind.X86_64.VgP384` states. -/

opaque low.x86_64.p384_vg.MulBase.check
  : Result (Option low.x86_64.p384_vg.MulBase)

opaque low.x86_64.p384_vg.MulBase.public_key
  : low.x86_64.p384_vg.MulBase → Array Std.U8 48#usize →
    Result (Option (Array Std.U8 97#usize))

opaque low.x86_64.p384_vg.Verify.check
  : Result (Option low.x86_64.p384_vg.Verify)

opaque low.x86_64.p384_vg.Verify.ecdsa_verify
  :
  low.x86_64.p384_vg.Verify → Array Std.U8 97#usize → Array Std.U8 48#usize →
    Array Std.U8 96#usize → Result Bool

opaque low.x86_64.p384_montjscalarmul.p384_montjscalarmul
  :
  Array Std.U64 18#usize → Array Std.U64 6#usize → Array Std.U64 18#usize
    → Result (Array Std.U64 18#usize)

opaque low.x86_64.p384_montjscalarmul_alt.p384_montjscalarmul_alt
  :
  Array Std.U64 18#usize → Array Std.U64 6#usize → Array Std.U64 18#usize
    → Result (Array Std.U64 18#usize)

opaque high.sec1.decode
  : Slice Std.U8 → high.asn1.ObjectId → Result (core.result.Result high.sec1.Decoded error.Error)

opaque high.sec1.decode_pkcs8
  : Slice Std.U8 → high.asn1.ObjectId → Result (core.result.Result high.sec1.Decoded error.Error)

opaque low.x86_64.bignum_mod_n384.bignum_mod_n384
  :
  Array Std.U64 6#usize → Array Std.U64 6#usize → Result (Array Std.U64
    6#usize)

opaque low.x86_64.p384_montjadd.p384_montjadd
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Array Std.U64 18#usize
    → Result (Array Std.U64 18#usize)

opaque low.x86_64.p384_montjadd_alt.p384_montjadd_alt
  :
  Array Std.U64 18#usize → Array Std.U64 18#usize → Array Std.U64 18#usize
    → Result (Array Std.U64 18#usize)

opaque high.curve.P256.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.oid
  : Result high.asn1.ObjectId

/-- P-256's ECDSA key generation, which the signing theorems model. -/
opaque high.curve.P256.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.generate_random_key
  {T0 : Type _} (midrngRandomSourceInst : mid.rng.RandomSource T0) :
  T0 → Result ((core.result.Result mid.p256.StaticPrivateKey error.Error) × T0)

opaque high.curve.P384.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.oid
  : Result high.asn1.ObjectId

/-- P-384's ECDSA key generation, which the signing theorems model. -/
opaque high.curve.P384.Insts.RindHighCurveCurveStaticPrivateKeyVerifyingKeyScalar.generate_random_key
  {T0 : Type _} (midrngRandomSourceInst : mid.rng.RandomSource T0) :
  T0 → Result ((core.result.Result mid.p384.StaticPrivateKey error.Error) × T0)

/-! P-256's s2n-bignum routines. -/

opaque low.x86_64.bignum_tomont_p256.bignum_tomont_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_tomont_p256_alt.bignum_tomont_p256_alt
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_demont_p256.bignum_demont_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_demont_p256_alt.bignum_demont_p256_alt
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_add_p256.bignum_add_p256
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_montmul_p256.bignum_montmul_p256
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_montmul_p256_alt.bignum_montmul_p256_alt
  :
  Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_montsqr_p256.bignum_montsqr_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_montsqr_p256_alt.bignum_montsqr_p256_alt
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_mod_n256.bignum_mod_n256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.p256_scalarmul.p256_scalarmul
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array Std.U64 8#usize →
    Result (Array Std.U64 8#usize)

opaque low.x86_64.p256_scalarmul_alt.p256_scalarmul_alt
  :
  Array Std.U64 8#usize → Array Std.U64 4#usize → Array Std.U64 8#usize →
    Result (Array Std.U64 8#usize)

opaque low.x86_64.bignum_inv_p256.bignum_inv_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.bignum_neg_p256.bignum_neg_p256
  : Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.p256_montjadd.p256_montjadd
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Array Std.U64 12#usize
    → Result (Array Std.U64 12#usize)

opaque low.x86_64.p256_montjadd_alt.p256_montjadd_alt
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Array Std.U64 12#usize
    → Result (Array Std.U64 12#usize)

opaque low.x86_64.p256_montjdouble.p256_montjdouble
  : Array Std.U64 12#usize → Array Std.U64 12#usize → Result (Array Std.U64 12#usize)

opaque low.x86_64.p256_montjdouble_alt.p256_montjdouble_alt
  : Array Std.U64 12#usize → Array Std.U64 12#usize → Result (Array Std.U64 12#usize)

opaque low.x86_64.p256_montjmixadd.p256_montjmixadd
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Array Std.U64 8#usize
    → Result (Array Std.U64 12#usize)

opaque low.x86_64.p256_montjmixadd_alt.p256_montjmixadd_alt
  :
  Array Std.U64 12#usize → Array Std.U64 12#usize → Array Std.U64 8#usize
    → Result (Array Std.U64 12#usize)

/-! ECDSA's scalar arithmetic mod n, s2n-bignum's generic routines. -/

opaque low.x86_64.bignum_modadd.bignum_modadd
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Result (Slice Std.U64)

opaque low.x86_64.bignum_demont.bignum_demont
  : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.bignum_modinv.bignum_modinv
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Result ((Slice Std.U64) × (Slice Std.U64))

/-! P-256's generator multiplication's mixed addition, aws-lc's. -/

opaque low.x86_64.ecp_nistz256.p256_point_add_affine
  : Array Std.U64 12#usize → Array Std.U64 8#usize → Result (Array Std.U64 12#usize)

/-! The HMAC-DRBG an ECDSA signature draws its nonces from. -/

opaque high.hmac_drbg.HmacDrbg.new
  {H : Type _} {Clause0_Context : Type _} {Clause0_State : Type _}
  (hashHashInst : high.hash.Hash H Clause0_Context Clause0_State) :
  Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
    Result (high.hmac_drbg.HmacDrbg H Clause0_Context Clause0_State)

opaque high.hmac_drbg.HmacDrbg.Insts.RindMidRngRandomSource.fill
  {H : Type _} {Clause0_Context : Type _} {Clause0_State : Type _}
  (hashHashInst : high.hash.Hash H Clause0_Context Clause0_State) :
  high.hmac_drbg.HmacDrbg H Clause0_Context Clause0_State → Slice Std.U8 →
    Result ((core.result.Result Unit error.Error) × (high.hmac_drbg.HmacDrbg H
    Clause0_Context Clause0_State) × (Slice Std.U8))

/-! The verifying key's caches of P, ..., 15P and 17P, ..., 31P, and the
signing key's of its encoded public key, which the ECDSA theorems take what
they need of as a hypothesis. -/

opaque low.generic.reuse_cache.ReuseCache.new
  {T : Type _} (coredefaultDefaultInst : core.default.Default T) :
  Result (low.generic.reuse_cache.ReuseCache T)

opaque low.generic.reuse_cache.ReuseCache.get_or_build_now
  {T : Type _} {T1 : Type _} (coremarkerCopyInst : core.marker.Copy T)
  (coredefaultDefaultInst : core.default.Default T)
  (coreopsfunctionFnOnceT1TupleTInst : core.ops.function.FnOnce T1 Unit T) :
  low.generic.reuse_cache.ReuseCache T → T1 → Result T

opaque low.generic.reuse_cache.ReuseCache.get_or_build
  {T : Type _} {T1 : Type _} (coredefaultDefaultInst : core.default.Default T)
  (coreopsfunctionFnOnceT1TupleTInst : core.ops.function.FnOnce T1 Unit T) :
  low.generic.reuse_cache.ReuseCache T → T1 → Result (Option T)

opaque low.generic.reuse_cache.ReuseCache.Insts.CoreCloneClone.clone
  {T : Type _} (coremarkerCopyInst : core.marker.Copy T)
  (coredefaultDefaultInst : core.default.Default T) :
  low.generic.reuse_cache.ReuseCache T → Result
    (low.generic.reuse_cache.ReuseCache T)

/-! P-256's key generation, which draws through a `dyn RandomSource`:
`Rind.X86_64.P256Dispatch` models it. -/

opaque mid.p256.PrivateKey.new_random
  : Result (core.result.Result mid.p256.PrivateKey error.Error)

/-! Whether the CPU runs pyca/verified-garbage's P-256, which reads no input,
and its routines behind their Rust wrappers, whose contracts
`Rind.X86_64.VgP256` states. -/

opaque low.x86_64.p256_vg.P256.check : Result (Option low.x86_64.p256_vg.P256)

opaque low.x86_64.p256_vg.P256.check_public_key : Result (Option low.x86_64.p256_vg.P256)

opaque low.x86_64.p256_vg.P256.public_key
  : low.x86_64.p256_vg.P256 → Array Std.U8 32#usize → Result (Option (Array Std.U8 65#usize))

opaque low.x86_64.p256_vg.P256.ecdh
  :
  low.x86_64.p256_vg.P256 → Array Std.U8 32#usize → Array Std.U8 65#usize → Result (Option
    (Array Std.U8 32#usize))

opaque low.x86_64.p256_vg.P256.verify
  :
  low.x86_64.p256_vg.P256 → Array Std.U8 65#usize → Array Std.U8 32#usize → Array Std.U8
    64#usize → Result Bool

/-! The other curves, which X25519's results never depend on. -/

opaque mid.p521.PrivateKey.new_random
  : Result (core.result.Result mid.p521.PrivateKey error.Error)

opaque mid.p384.PrivateKey.new_random
  : Result (core.result.Result mid.p384.PrivateKey error.Error)

opaque mid.p521.PrivateKey.public_key_uncompressed
  : mid.p521.PrivateKey → Result (Array Std.U8 133#usize)

opaque mid.p521.PrivateKey.diffie_hellman
  :
  mid.p521.PrivateKey → mid.p521.PublicKey → Result (core.result.Result
    mid.p521.SharedSecret error.Error)

opaque mid.p521.PublicKey.from_x962_uncompressed
  : Slice Std.U8 → Result (core.result.Result mid.p521.PublicKey error.Error)


/-! MD5, which no proof covers. -/

opaque mid.md5.Md5State.new : Result mid.md5.Md5State

opaque mid.md5.Md5State.finish_with
  : mid.md5.Md5State → Slice Std.U8 → Result (Array Std.U8 16#usize)

opaque mid.md5.Md5Context.new : Result mid.md5.Md5Context

opaque mid.md5.Md5Context.update : mid.md5.Md5Context → Slice Std.U8 → Result mid.md5.Md5Context

opaque mid.md5.Md5Context.finish : mid.md5.Md5Context → Result (Array Std.U8 16#usize)

opaque mid.md5.Md5Context.Insts.CoreCloneClone.clone : mid.md5.Md5Context → Result mid.md5.Md5Context

/-! Agreement key encodings, and loading on the curves no theorem loads a key
on, whose DER no proof covers. -/

opaque high.agreement.x25519_from_pkcs8
  : high.agreement.Algorithm → Slice Std.U8 →
    Result (core.result.Result (mid.x25519.PrivateKey × high.agreement.PublicKey) error.Error)

opaque high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.x25519.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.agreement.X25519Curve.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.x25519.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.p256.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P256.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.p256.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.p384.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P384.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.p384.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P521.Insts.RindHighAgreementAgreePrivateKey.encode_pkcs8
  : mid.p521.PrivateKey → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P521.Insts.RindHighAgreementAgreePrivateKey.encode_scalar
  : mid.p521.PrivateKey → Slice Std.U8 →
    Result ((core.result.Result (Slice Std.U8) error.Error) × (Slice Std.U8))

opaque high.curve.P521.Insts.RindHighAgreementAgreePrivateKey.load
  : high.agreement.Algorithm → high.agreement.Source →
    Result (core.result.Result (mid.p521.PrivateKey × high.agreement.PublicKey) error.Error)

/-! s2n-bignum's routines for RSA, transliterated to inline assembly. -/

opaque low.x86_64.bignum_negmodinv.bignum_negmodinv
  : Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.bignum_montifier.bignum_montifier
  : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result ((Slice Std.U64) × (Slice Std.U64))

opaque low.x86_64.bignum_bitsize.bignum_bitsize
  : Slice Std.U64 → Result Std.Usize

opaque low.x86_64.bignum_optsub.bignum_optsub
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Std.U64 → Result
    (Slice Std.U64)

opaque low.x86_64.bignum_emontredc_8n.bignum_emontredc_8n
  :
  Slice Std.U64 → Slice Std.U64 → Std.U64 → Result (Std.U64 × (Slice
    Std.U64))

opaque low.x86_64.bignum_kmul_16_32.bignum_kmul_16_32
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Array Std.U64 32#usize
    → Result ((Slice Std.U64) × (Array Std.U64 32#usize))

opaque low.x86_64.bignum_kmul_32_64.bignum_kmul_32_64
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Array Std.U64 96#usize
    → Result ((Slice Std.U64) × (Array Std.U64 96#usize))

opaque low.x86_64.bignum_ksqr_16_32.bignum_ksqr_16_32
  :
  Slice Std.U64 → Slice Std.U64 → Array Std.U64 24#usize → Result ((Slice
    Std.U64) × (Array Std.U64 24#usize))

opaque low.x86_64.bignum_ksqr_32_64.bignum_ksqr_32_64
  :
  Slice Std.U64 → Slice Std.U64 → Array Std.U64 72#usize → Result ((Slice
    Std.U64) × (Array Std.U64 72#usize))

opaque low.x86_64.bignum_montmul.bignum_montmul
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Result (Slice Std.U64)

opaque low.x86_64.bignum_montredc.bignum_montredc
  : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.bignum_modsub.bignum_modsub
  : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.bignum_mul.bignum_mul
  : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.bignum_add.bignum_add
  : Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Result (Std.U64 × (Slice Std.U64))

opaque low.x86_64.bignum_digitsize.bignum_digitsize
  : Slice Std.U64 → Result Std.Usize

opaque low.x86_64.bignum_copy_row_from_table.bignum_copy_row_from_table
  : Slice Std.U64 → Slice Std.U64 → Std.U64 → Std.U64 → Std.U64 → Result (Slice Std.U64)

/-! aws-lc's Montgomery products, behind their Rust wrappers, which
`Rind.X86_64.RsaMont` states: `nohw_spec` restates rind's HOL Light proof of
`bn_mul_mont_nohw`, `mul4x_spec` and `mulx4x_spec` its Lean proofs of
`bn_mul4x_mont` and `bn_mulx4x_mont`, `sqrx8x_spec` its Lean proof of
`bn_sqrx8x_mont`, and `AwsLcMont` `bn_sqr8x_mont` without BMI2 and ADX for
the theorems that need it. -/

opaque low.x86_64.mont.nohw
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Std.U64 → Result (Slice Std.U64)

opaque low.x86_64.mont.mul4x
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Slice Std.U64 →
    Std.U64 → Option low.x86_64.cpu.HaveBmi2Adx → Result (Slice Std.U64)

opaque low.x86_64.mont.sqr8x
  :
  Slice Std.U64 → Slice Std.U64 → Slice Std.U64 → Std.U64 → Option
    low.x86_64.cpu.HaveBmi2Adx → Result (Slice Std.U64)

/-! aws-lc's `bn_power5` and `bn_powerx5`, which `mont_exp`'s Rust runs at each
width that is a multiple of eight words, but for 16 and 32 with BMI2 and ADX,
and the RSAZ exponentiations, which `PosInt` runs in place of `mont_exp` only
without ADX or at the widths its AVX-512 IFMA path takes. No proof covers
them, and none reaches them: each theorem's hypotheses rule out the paths
that call them. -/

opaque low.x86_64.mont_exp.power5
  : Slice Std.U64 → Slice low.x86_64.mont_exp.Row → Slice Std.U64 → Std.U64 → Std.U64 →
    Option low.x86_64.cpu.HaveBmi2Adx → Result (Slice Std.U64)

opaque low.x86_64.mont_exp.power5_table
  : Slice Std.U64 → Std.Usize → Std.Usize → Result (alloc.vec.Vec low.x86_64.mont_exp.Row)

opaque low.posint.PosInt.mod_exp_rsaz {N : Std.Usize}
  : low.posint.PosInt N → low.x86_64.rsaz.Rsaz → low.posint.PosInt N → low.posint.PosInt N →
    low.posint.PosInt N → Std.U64 → Result (Option (low.posint.PosInt N))

opaque low.posint.PosInt.mod_exp_pair_rsaz {N : Std.Usize}
  : low.x86_64.rsaz_avx512.RsazAvx512 → low.posint.ModExp N → low.posint.ModExp N →
    Result ((low.posint.PosInt N) × (low.posint.PosInt N))

/-! ML-KEM's polynomial routines, behind their Rust wrappers, which pick a
path from the CPU: with AVX2, s2n-bignum's routines, mlkem-native's code
with the AVX2 layout's tables, and mlkem-native's AVX2 compression;
without it, `low::generic::mlkem_poly`, a port of mlkem-native's portable
C, and for 12-bit unpacking and compression `low::generic::mlkem`'s Rust,
whose unpacking `Rind/Aarch64/MlKemGeneric.lean` proves on aarch64; its
reordering is a no-op, since that path keeps the natural order. -/

opaque low.x86_64.mlkem.mlkem_ntt
  : Array Std.I16 256#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_intt
  : Array Std.I16 256#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_mulcache_compute
  : Array Std.I16 128#usize → Array Std.I16 256#usize → Result (Array Std.I16 128#usize)

opaque low.x86_64.mlkem.mlkem_rej_uniform_vartime
  : Array Std.I16 256#usize → Slice Std.U8 → Result (Std.U64 × (Array Std.I16 256#usize))

opaque low.x86_64.mlkem.mlkem_basemul_k2
  : Array Std.I16 256#usize → Array Std.I16 512#usize → Array Std.I16 512#usize →
    Array Std.I16 256#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_basemul_k3
  : Array Std.I16 256#usize → Array Std.I16 768#usize → Array Std.I16 768#usize →
    Array Std.I16 384#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_basemul_k4
  : Array Std.I16 256#usize → Array Std.I16 1024#usize → Array Std.I16 1024#usize →
    Array Std.I16 512#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_reduce
  : Array Std.I16 256#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_tomont
  : Array Std.I16 256#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_frombytes
  : Array Std.I16 256#usize → Array Std.U8 384#usize → Result (Array Std.I16 256#usize)

opaque low.x86_64.mlkem.mlkem_tobytes
  : Array Std.U8 384#usize → Array Std.I16 256#usize → Result (Array Std.U8 384#usize)

opaque low.x86_64.mlkem.mlkem_compress_d4
  : Array Std.U8 128#usize → Array Std.I16 256#usize → Result (Array Std.U8 128#usize)

opaque low.x86_64.mlkem.mlkem_compress_d5
  : Array Std.U8 160#usize → Array Std.I16 256#usize → Result (Array Std.U8 160#usize)

opaque low.x86_64.mlkem.mlkem_compress_d10
  : Array Std.U8 320#usize → Array Std.I16 256#usize → Result (Array Std.U8 320#usize)

opaque low.x86_64.mlkem.mlkem_compress_d11
  : Array Std.U8 352#usize → Array Std.I16 256#usize → Result (Array Std.U8 352#usize)

opaque low.x86_64.mlkem.mlkem_unpack
  : Array Std.I16 256#usize → Result (Array Std.I16 256#usize)

/-- ML-KEM-1024's eight-way matrix sampler, which hands the eight-way Keccak
function pointers Aeneas cannot translate. No ✓ covers ML-KEM-1024. -/
opaque mid.mlkem.sample_ntt.sample_ntt_8x
  : Array Std.U8 32#usize → Bool → Slice (Array Std.I16 256#usize) →
    Result (Slice (Array Std.I16 256#usize))

/-- ML-KEM-1024's eight-way CBD sampler, which hands the eight-way SHAKE256
a function pointer Aeneas cannot translate. No ✓ covers ML-KEM-1024. -/
opaque mid.mlkem.sample_poly_cbd2_8x
  : Array Std.U8 32#usize → Std.U8 → Std.Usize →
    Result (Array (Array Std.I16 256#usize) 8#usize)

/-! pyca/verified-garbage's ML-KEM-768 routines, behind their Rust wrappers,
whose contracts `Rind.X86_64.VgMlKem` states, and the checks for the CPU
features they need. -/

opaque low.x86_64.mlkem768_vg.Encaps.check : Result (Option low.x86_64.mlkem768_vg.Encaps)

opaque low.x86_64.mlkem768_vg.KeyPair.check : Result (Option low.x86_64.mlkem768_vg.KeyPair)

opaque low.x86_64.mlkem768_vg.Encaps.check_ek
  : low.x86_64.mlkem768_vg.Encaps → Array Std.U8 1184#usize → Result Bool

opaque low.x86_64.mlkem768_vg.Encaps.encaps
  :
  low.x86_64.mlkem768_vg.Encaps → Array Std.U8 1184#usize → Option (Array
    Std.U8 32#usize) → Array Std.U8 32#usize → Result (Option ((Array
    Std.U8 32#usize) × (Array Std.U8 1088#usize)))

opaque low.x86_64.mlkem768_vg.KeyPair.keygen
  :
  low.x86_64.mlkem768_vg.KeyPair → Array Std.U8 64#usize → Result (Option
    (Array Std.U8 2400#usize))

opaque low.x86_64.mlkem768_vg.KeyPair.decaps
  :
  low.x86_64.mlkem768_vg.KeyPair → Array Std.U8 2400#usize → Array Std.U8
    1088#usize → Result (Option (Array Std.U8 32#usize))

/-! RSA's DER parsing and encoding, which the ✓ leaves out. -/

opaque high.rsa.pkcs1_components
  :
  Slice Std.U8 → Result (core.result.Result ((Slice Std.U8) × (Slice
    Std.U8)) error.Error)

opaque high.rsa.spki_components
  :
  Slice Std.U8 → Result (core.result.Result ((Slice Std.U8) × (Slice
    Std.U8)) error.Error)

opaque high.rsa.VerifyingKey.to_pkcs1_der
  :
  high.rsa.VerifyingKey → Slice Std.U8 → Result ((core.result.Result (Slice
    Std.U8) error.Error) × (Slice Std.U8))

/-- Whether the CPU runs pyca/verified-garbage's AVX-512 IFMA X25519 and
Ed25519, and the wrappers of those routines, whose contracts
`Rind.X86_64.VgCurve25519` restates. -/
opaque low.x86_64.curve25519_ifma.Curve25519Ifma.check : Result (Option low.x86_64.curve25519_ifma.Curve25519Ifma)

opaque low.x86_64.curve25519_ifma.Curve25519Ifma.x25519
  : low.x86_64.curve25519_ifma.Curve25519Ifma → Array Std.U64 4#usize → Array Std.U64 4#usize → Array Std.U64 4#usize →
    Result (Array Std.U64 4#usize)

opaque low.x86_64.curve25519_ifma.Curve25519Ifma.x25519_base
  : low.x86_64.curve25519_ifma.Curve25519Ifma → Array Std.U64 4#usize → Array Std.U64 4#usize → Result (Array Std.U64 4#usize)

opaque low.x86_64.curve25519_ifma.Curve25519Ifma.ed25519_key_pair
  : low.x86_64.curve25519_ifma.Curve25519Ifma → Array Std.U8 32#usize → Result (Array Std.U8 64#usize × Array Std.U8 32#usize)

opaque low.x86_64.curve25519_ifma.Curve25519Ifma.ed25519_sign
  : low.x86_64.curve25519_ifma.Curve25519Ifma → Array Std.U8 64#usize → Array Std.U8 32#usize → Slice Std.U8 →
    Result (Array Std.U8 64#usize)

opaque low.x86_64.curve25519_ifma.Curve25519Ifma.ed25519_verify
  : low.x86_64.curve25519_ifma.Curve25519Ifma → Array Std.U8 32#usize → Slice Std.U8 → Array Std.U8 64#usize → Result Bool

end rind.x86_64
