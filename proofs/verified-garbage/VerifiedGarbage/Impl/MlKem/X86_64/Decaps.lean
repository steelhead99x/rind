module

public import VerifiedGarbage.Impl.MlKem.X86_64.Encrypt

/-!
# ML-KEM on x86-64: decapsulation (`vg_mlkem768_decaps`, `vg_mlkem1024_decaps`)

`kemDecaps L (dk = rdi, ct = rsi, key = rdx, scratch = rcx) -> eax`:
`ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm 18) of the parameter set
`L` (rank `k`). It keeps `scratch` in `rbx`, `dk` in `rbp`, `ct` in `r14` and
`key` in `r12`, and saves its caller's values of them (and of `r13` and
`r15`) in `scratch`.

1. `m' = K-PKE.Decrypt(dk[0 : 384k], c)` (Algorithm 15) to `M`:
   `u'[i] = Decompress_{d_u}(ByteDecode_{d_u}(c[32 d_u i : 32 d_u (i + 1)]))`
   (polynomial `i`); `ŝ[i] = ByteDecode₁₂(dk[384i : 384i + 384])`
   (polynomial `k + i`); `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` (polynomial 15) in one call
   of `vg_mlkem*_decrypt_mul`, with polynomials `2k` to `2k + 3` as its
   working space; `w = v' - NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` with
   `v' = Decompress_{d_v}(ByteDecode_{d_v}(c[32 d_u k :]))` (polynomial 16),
   and `m' = ByteEncode₁(Compress₁(w))`.
2. `(K', r') = G(m' ‖ h)` to `G`, with `h = dk[768k + 32 : 768k + 64]`, and
   `K̄ = J(z ‖ c)` to `KB`, with `z = dk[768k + 64 : 768k + 96]`.
3. `c' = K-PKE.Encrypt(ek, m', r')` to `CT` (`Encrypt.lean`), with `ek` at
   `dk + 384k`.
4. The key `K'` if `c = c'`, and `K̄` otherwise, to `key`, without a branch:
   `rdx` is the OR of the XORs of the words (8 bytes) of `c` and `c'`, so 0 exactly
   when they are equal (`sub rdx, 1` borrows then), and `rax` the mask
   `-borrow`; each byte of `key` is `((K' ⊕ K̄) ∧ mask) ⊕ K̄`.

It returns `r15`: 0 if a `SampleNTT` failed (when `key` is unspecified), and
1 otherwise.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Decaps

variable (L : Kem)

def pro : List Instr := topPro .rcx [(.rbp, .rdi), (.r14, .rsi), (.r12, .rdx)]

/-- `u'[i]`. -/
def uHat (A : Arith) (i : Nat) : Prog isa := L.ddAt A.codecs (.r14, 32 * L.du * i) L.du (pS i)

/-- `ŝ[i]`. -/
def sHat (A : Arith) (i : Nat) : Prog isa := dec12At A (.rbp, 384 * i) (pS (L.k + i))

/-- `m'` to `M`. -/
def decrypt (A : Arith) : Prog isa :=
  .seq (seqR (uHat L A) 0 L.k) (.seq (seqR (sHat L A) 0 L.k) (.seq (L.decMulAt A (pS 15) (pS L.k) (pS 0) (pS (2 * L.k)))
    (.seq (L.ddAt A.codecs (.r14, 32 * L.du * L.k) L.dv (pS 16)) (.seq (subAt A (pS 16) (pS 15))
      (ceAt A.codecs (pS 16) 1 (sc oM))))))

/-- `G(m' ‖ h)` and `J(z ‖ c)`. -/
def hashes : Prog isa :=
  .seq (hashAt [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)] 72 6 (sc oG) 64)
    (hashAt [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)] 136 0x1f (sc oKB) 32)

/-- The OR of the XORs of the words of `c` and `c'`, to `rdx`. -/
def cmpBody : Prog isa :=
  .block [.mov .rax (.mem (at_ .rsi 0)), .mov .r8 (.mem (at_ .rdi 0)), .alu .xor .rax (.reg .r8),
    .alu .or .rdx (.reg .rax), .alu .add .rsi (.imm 8), .alu .add .rdi (.imm 8), .alu .sub .rcx (.imm 1)]

/-- A byte of the key, `((K' ⊕ K̄) ∧ mask) ⊕ K̄`. -/
def selBody : Prog isa :=
  .block [.movzx8 .r9 (at_ .rsi 0), .movzx8 .r10 (at_ .rdi 0), .alu .xor .r9 (.reg .r10), .alu .and .r9 (.reg .rax),
    .alu .xor .r9 (.reg .r10), .store8 (at_ .r8 0) .r9, .alu .add .rsi (.imm 1), .alu .add .rdi (.imm 1),
    .alu .add .r8 (.imm 1), .alu .sub .rcx (.imm 1)]

/-- The key `K'` if `c = c'`, for the `n` bytes of `c'` at `scratch + o`, and `K̄` otherwise. -/
def selectAt (o n : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 o)),
      .mov32 .rcx (.imm (BitVec.ofNat 32 (n / 8))), .mov32 .rdx (.imm 0)])
    (.seq (.loop cmpBody .ne)
      (.seq (.block [.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .mov .rsi (.reg .rbx),
          .alu .add .rsi (.imm (BitVec.ofNat 32 oG)), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oKB)),
          .mov .r8 (.reg .r12), .mov32 .rcx (.imm 32)])
        (.loop selBody .ne)))

/-- `selectAt`, with `c'` where the re-encryption writes it (`oCT`). -/
abbrev select : Prog isa := selectAt L.oCT L.ctLen

end Decaps

open Decaps in
/-- The decapsulation of the parameter set `L`. -/
def kemDecaps (L : Kem) (c : Callee4) : Prog isa :=
  .seq (.block pro) (.seq (decrypt L c.arith) (.seq (hashes L) (.seq (encrypt L c (.rbp, 384 * L.k))
    (.seq (select L) (.block topEpi)))))


end VG.Impl.MlKem.X86_64
