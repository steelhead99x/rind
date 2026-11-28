module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kem
public import VerifiedGarbage.Impl.MlKem.X86_64.Arith16

/-!
# ML-KEM on x86-64: K-PKE in one call, with 16-bit polynomials

`vg_mlkem*_kpke_decrypt(m = rdi, s = rsi, ct = rdx, scratch = rcx)`
(`Proof/MlKem/Kpke16Contract.lean`): `K-PKE.Decrypt(dk_PKE, c)` (FIPS 203
Algorithm 15) of the parameter set `L`, with the arithmetic of `A`, calling
no function: it runs the code of the polynomial primitives inline, one
after the other, on polynomials in `scratch`, and the code of
`vg_mlkem*_decrypt_mul` but for its restore of the registers it saves
(`dm`, which leaves `rbx` and `r15` as they were). It keeps `scratch` in
`rbx`, `s` in `rbp` and `ct` in `r13` until the product, and `m` in `r15`,
and saves its caller's callee-saved registers at `scratch + 14336`.

The layout of `scratch` (16 KiB): the working space of
`vg_mlkem*_decrypt_mul` at 0 (4096 bytes; it saves registers at 3072); `u'[i]` in polynomial `i`
(`qP i`, 1024 bytes each from 4096), `ŝ[i]` in polynomial `k + i`,
`NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` in polynomial `2k` and `v'` in polynomial `2k + 1`;
the saved registers at 14336.

1. `u'[i] = Decompress_{d_u}(ByteDecode_{d_u}(c[32 d_u i : 32 d_u (i + 1)]))`;
2. `ŝ[i] = ByteDecode₁₂(dk_PKE[384i : 384i + 384])`;
3. `v' = Decompress_{d_v}(ByteDecode_{d_v}(c[32 d_u k :]))`;
4. `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` (the code of `vg_mlkem*_decrypt_mul`, with its own
   MXCSR region);
5. `w = v' - NTT⁻¹(ŝ^⊺ ∘ NTT(u'))`, and `m = ByteEncode₁(Compress₁(w))`.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Kpke16

/-- The saved registers. -/
def oKS : Nat := 14336

/-- Polynomial `i` of the working space. -/
def oQ (i : Nat) : Nat := 4096 + 1024 * i

/-- Polynomial `i` of the working space, as a pointer. -/
abbrev qP (i : Nat) : Ptr := (.rbx, oQ i)

/-- The callee-saved registers the function changes. -/
def kRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Save `kRegs` at `scratch + oKS`, and move the arguments to them. -/
def pro : List Instr :=
  (List.range 6).map (fun i => .store (at_ .rcx (oKS + 8 * i)) (kRegs.getD i .rbx)) ++
    [.mov .rbx (.reg .rcx), .mov .rbp (.reg .rsi), .mov .r15 (.reg .rdi), .mov .r13 (.reg .rdx)]

/-- Restore `kRegs` (`rbx` last). -/
def epi : List Instr :=
  [.mov .r15 (.mem (at_ .rbx (oKS + 40))), .mov .r14 (.mem (at_ .rbx (oKS + 32))),
    .mov .r13 (.mem (at_ .rbx (oKS + 24))), .mov .r12 (.mem (at_ .rbx (oKS + 16))),
    .mov .rbp (.mem (at_ .rbx (oKS + 8))), .mov .rbx (.mem (at_ .rbx oKS))]

/-- The code of `vg_mlkem*_decrypt_mul` of rank `k`, with `inner`, but for
the restore of the registers it saves. -/
def dmBody (inner : Nat → Prog isa) (k : Nat) : Prog isa :=
  .seq (.block (KpkeMul.save ++ [.mov .rbx (.reg .rcx), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi),
      .mov .r13 (.reg .rdx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (inner k)

/-- `ŝᵀ ∘ NTT(u)` with AVX2: each `NTT(u[j])` to an
accumulator, then the row of products and `NTT⁻¹`. -/
def dmInnerY (k : Nat) : Prog isa :=
  .seq (.block KpkeMul.startY) (.seq (.loop KpkeMul.nttTermY .ne) (KpkeMul.rowInvY [.mov .rsi (.reg .r12)] 1024 k))

variable (L : Kem) (A : Prims) (inner : Nat → Prog isa)

/-- `Decompress_d(ByteDecode_d(b))` to `f`, inline, for `d = d_u` or `d_v`. -/
def ddIn (b : Ptr) (d : Nat) (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi b ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))), .mov32 .rdx (.imm (BitVec.ofNat 32 d))] ++
      lea .rcx f))
    (L.dd A.codecs)

/-- `u'[i]`. -/
def uHat (i : Nat) : Prog isa := ddIn L A (.r13, 32 * L.du * i) L.du (qP i)

/-- `ŝ[i]`. -/
def sHat (i : Nat) : Prog isa := .seq (.block (lea .rdi (.rbp, 384 * i) ++ lea .rsi (qP (L.k + i)))) A.dec12

/-- `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` to polynomial `2k`. -/
def prod : Prog isa :=
  .seq (.block (lea .rdi (qP (2 * L.k)) ++ lea .rsi (qP L.k) ++ lea .rdx (qP 0) ++ lea .rcx (.rbx, 0)))
    (dmBody inner L.k)

/-- `v'` to polynomial `2k + 1`. -/
def vHat : Prog isa := ddIn L A (.r13, 32 * L.du * L.k) L.dv (qP (2 * L.k + 1))

/-- `w = v' - NTT⁻¹(ŝ^⊺ ∘ NTT(u'))`, in polynomial `2k + 1`. -/
def wSub : Prog isa := .seq (.block (lea .rdi (qP (2 * L.k + 1)) ++ lea .rsi (qP (2 * L.k)))) A.sub

/-- `m = ByteEncode₁(Compress₁(w))`. -/
def mOut : Prog isa :=
  .seq (.block (lea .rdi (qP (2 * L.k + 1)) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 1))] ++ lea .rdx (.r15, 0) ++
      [.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * 1)))]))
    A.codecs.ce

/-- The body, between `pro` and `epi`. -/
def decBody : Prog isa :=
  .seq (seqR (uHat L A) 0 L.k) (.seq (seqR (sHat L A) 0 L.k)
    (.seq (vHat L A) (.seq (prod L inner) (.seq (wSub L A) (mOut L A)))))

/-! ## `vg_mlkem*_kpke_encrypt` -/

/-- The saved registers of `kpkeEnc`. -/
def oKSE : Nat := 19456

/-- Save `kRegs` at `scratch + oKSE`, and move the arguments to them:
`ct` to `r15`, `a` to `rbp`, `t` to `r12`, `r` to `r13`, `m` to `r14`. -/
def proE : List Instr :=
  (List.range 6).map (fun i => .store (at_ .r9 (oKSE + 8 * i)) (kRegs.getD i .rbx)) ++
    [.mov .rbx (.reg .r9), .mov .r15 (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8)]

/-- Restore `kRegs` (`rbx` last). -/
def epiE : List Instr :=
  [.mov .r15 (.mem (at_ .rbx (oKSE + 40))), .mov .r14 (.mem (at_ .rbx (oKSE + 32))),
    .mov .r13 (.mem (at_ .rbx (oKSE + 24))), .mov .r12 (.mem (at_ .rbx (oKSE + 16))),
    .mov .rbp (.mem (at_ .rbx (oKSE + 8))), .mov .rbx (.mem (at_ .rbx oKSE))]

/-- The polynomial of `u16`s at `b` as `u32`s in `f`, inline. -/
def widenIn (b f : Ptr) : Prog isa := .seq (.block (lea .rdx b ++ lea .r9 f)) vunpack

/-- `t̂[i] = ByteDecode₁₂(ek_PKE[384i : 384i + 384])`, to polynomial `k + i`. -/
def tHatE (i : Nat) : Prog isa := .seq (.block (lea .rdi (.r12, 384 * i) ++ lea .rsi (qP (L.k + i)))) A.dec12

/-- `y[j]` (`s[j]` and `e[j]` in `kpkeKg`), to polynomial `j`. -/
def yE (j : Nat) : Prog isa := widenIn (.r13, 512 * j) (qP j)

/-- `NTT⁻¹(Â^⊺ ∘ ŷ)` and `NTT⁻¹(t̂^⊺ ∘ ŷ)`, to the `k + 1` polynomials from
`2k`: the code of `vg_mlkem*_encrypt_mul` (`mul`), from `a` and from `y`
(the first `k` polynomials of `r`). -/
def prodE (mul : Nat → Prog isa) : Prog isa :=
  .seq (.block (lea .rdi (qP (2 * L.k)) ++ lea .rsi (.rbp, 0) ++ lea .rdx (qP L.k) ++ lea .rcx (.r13, 0) ++
    lea .r8 (.rbx, 0))) (mul L.k)

/-- `f += g`, inline. -/
def addIn (f g : Ptr) : Prog isa := .seq (.block (lea .rdi f ++ lea .rsi g)) A.add

/-- The polynomial for `μ`. -/
abbrev eP (L : Kem) : Ptr := qP (3 * L.k + 1)

/-- `f += g`, inline, with `g` of `u16`s. -/
def add16In (f g : Ptr) : Prog isa := .seq (.block (lea .rdi f ++ lea .rsi g)) add16Y

/-- `u[i] = NTT⁻¹(Â^⊺ ∘ ŷ)[i] + e₁[i]`, and `ByteEncode_{d_u}(Compress_{d_u}(u[i]))` to `c₁`
(`L.ceU`). -/
def uE (i : Nat) : Prog isa :=
  .seq (add16In (qP (2 * L.k + i)) (.r13, 512 * (L.k + i)))
    (.seq (.block (lea .rdi (qP (2 * L.k + i)) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 L.du))] ++
      lea .rdx (.r15, 32 * L.du * i) ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * L.du)))]))
      L.ceU)

/-- `v = NTT⁻¹(t̂^⊺ ∘ ŷ) + e₂ + μ`, and `ByteEncode_{d_v}(Compress_{d_v}(v))` to `c₂`
(`L.ceV`). -/
def vE : Prog isa :=
  .seq (add16In (qP (3 * L.k)) (.r13, 512 * (2 * L.k)))
    (.seq (.seq (.block (lea .rdi (.r14, 0) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * 1))),
        .mov32 .rdx (.imm (BitVec.ofNat 32 1))] ++ lea .rcx (eP L))) A.codecs.dd) (.seq (addIn A (qP (3 * L.k)) (eP L))
      (.seq (.block (lea .rdi (qP (3 * L.k)) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 L.dv))] ++
        lea .rdx (.r15, 32 * L.du * L.k) ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * L.dv)))]))
        L.ceV)))

/-- The prologue, `t̂` and the products, with the code `mul` of the products. -/
def kpkeEncPre (mul : Nat → Prog isa) : Prog isa :=
  .seq (.block proE) (.seq (seqR (tHatE L A) 0 L.k) (prodE L mul))

/-- `u` and `v`, with the multiplications of their compressions (`L.ceU`,
`L.ceV`), and the epilogue. -/
def kpkeEncPost : Prog isa :=
  .seq (.seq (seqR (uE L) 0 L.k) (vE L A)) (.block epiE)

/-! ## `vg_mlkem*_kpke_keygen` -/

/-- Save `kRegs` at `scratch + oKSE`, and move the arguments to them: `ek`
to `r15`, `dk` to `rbp`, `a` to `r12` and `se` to `r13`. -/
def proG : List Instr :=
  (List.range 6).map (fun i => .store (at_ .r8 (oKSE + 8 * i)) (kRegs.getD i .rbx)) ++
    [.mov .rbx (.reg .r8), .mov .r15 (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx)]

/-- `ŝ = NTT(s)` in place and `t̂ = Â ∘ ŝ + NTT(e)` to the `k` polynomials from
`2k`: the code of `vg_mlkem*_keygen_mul` (`mul`), from `a` and `e` (`u16`s,
the last `k` polynomials of `se`). -/
def prodG (mul : Nat → Prog isa) : Prog isa :=
  .seq (.block (lea .rdi (qP (2 * L.k)) ++ lea .rsi (qP 0) ++ lea .rdx (.r12, 0) ++ lea .rcx (.r13, 512 * L.k) ++
    lea .r8 (.rbx, 0))) (mul L.k)

/-- `ByteEncode₁₂(t̂[i])` to `ek`. -/
def ekOut (i : Nat) : Prog isa := .seq (.block (lea .rdi (qP (2 * L.k + i)) ++ lea .rsi (.r15, 384 * i))) A.enc12

/-- `ByteEncode₁₂(ŝ[j])` to `dk`. -/
def dkOut (j : Nat) : Prog isa := .seq (.block (lea .rdi (qP j) ++ lea .rsi (.rbp, 384 * j))) A.enc12

/-- The prologue, `s` as `u32`s (polynomials `0, …, k - 1`), and the products,
with the code `mul` of `vg_mlkem*_keygen_mul`. -/
def kpkeKgPre (mul : Nat → Prog isa) : Prog isa :=
  .seq (.block proG) (.seq (seqR yE 0 L.k) (prodG L mul))

/-- `ek`, `dk` and the epilogue. -/
def kpkeKgPost : Prog isa := .seq (seqR (ekOut L A) 0 L.k) (.seq (seqR (dkOut A) 0 L.k) (.block epiE))

end Kpke16

open Kpke16 in
/-- `vg_mlkem*_kpke_decrypt` of the parameter set `L`, with the arithmetic of `A`
and the code `inner` of its products. -/
def kpkeDec (L : Kem) (A : Prims) (inner : Nat → Prog isa) : Prog isa :=
  .seq (.block pro) (.seq (decBody L A inner) (.block epi))

open Kpke16 in
/-- `vg_mlkem*_kpke_encrypt` of the parameter set `L`, with the arithmetic of
`A` and the code `mul` of `vg_mlkem*_encrypt_mul` (reading `Â` as `u16`s). -/
def kpkeEnc (L : Kem) (A : Prims) (mul : Nat → Prog isa) : Prog isa := .seq (kpkeEncPre L A mul) (kpkeEncPost L A)

open Kpke16 in
/-- `vg_mlkem*_kpke_keygen` of the parameter set `L`, with the arithmetic of
`A` and the code `mul` of `vg_mlkem*_keygen_mul` (reading `Â` as `u16`s). -/
def kpkeKg (L : Kem) (A : Prims) (mul : Nat → Prog isa) : Prog isa := .seq (kpkeKgPre L mul) (kpkeKgPost L A)

/-! ## Calls of the K-PKE functions -/

/-- `vg_mlkem*_kpke_keygen(ek, dk, a, se, scratch)`. -/
def Kem.kpkeKgAt (L : Kem) (ek dk a se z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi ek ++ lea .rsi dk ++ lea .rdx a ++ lea .rcx se ++ lea .r8 z))
    (.call (L.p.fn "kpke_keygen") (kpkeKg L .avx2 keygenMul16Y))

/-- `vg_mlkem*_kpke_encrypt(ct, a, t, r, m, scratch)`. -/
def Kem.kpkeEncAt (L : Kem) (ct a t r m z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi ct ++ lea .rsi a ++ lea .rdx t ++ lea .rcx r ++ lea .r8 m ++ lea .r9 z))
    (.call (L.p.fn "kpke_encrypt") (kpkeEnc L .avx2 encryptMul16Y))

/-- `vg_mlkem*_kpke_decrypt(m, s, ct, scratch)`. -/
def Kem.kpkeDecAt (L : Kem) (m s ct z : Ptr) : Prog isa :=
  .seq (.block (lea .rdi m ++ lea .rsi s ++ lea .rdx ct ++ lea .rcx z))
    (.call (L.p.fn "kpke_decrypt") (kpkeDec L .avx2 Kpke16.dmInnerY))

end VG.Impl.MlKem.X86_64
