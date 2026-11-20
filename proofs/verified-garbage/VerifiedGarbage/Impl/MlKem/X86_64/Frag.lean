module

public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeMul
public import VerifiedGarbage.Impl.MlKem.X86_64.Encode12
public import VerifiedGarbage.Impl.MlKem.X86_64.Encode12Avx2
public import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16Avx2
public import VerifiedGarbage.Impl.MlKem.X86_64.CompressAvx2
public import VerifiedGarbage.Impl.MlKem.X86_64.SampleH
public import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16

/-!
# ML-KEM on x86-64: the pieces of the top-level functions

The key generation, encapsulation and decapsulation of each parameter set
(`Kem.lean`) are
sequences of calls of the polynomial primitives and the SHA-3 sponge
functions, on buffers in their working space `scratch` (whose address they
keep in `rbx`) and their arguments (whose addresses they keep in `rbp`,
`r12`, `r13` and `r14`): all callee-saved registers, which the functions
they call preserve. A buffer is at `p.1 + p.2` for a pointer `p` (a
register and an offset). Each call is preceded by the moves of its
arguments into their registers (`lea`, a `mov` and an `add`).

The layout of `scratch` (in bytes): the Keccak state at 0 (200 bytes) and
the sponge functions' working space at 200 (640 bytes); the caller's
callee-saved registers at 840 (48 bytes); a byte (`NB`, an index) at 896
and the seed of `SampleNTT` (`SB`, 34 bytes) at 904; the output of `G` at
1024 (64 bytes), of `H` at 1088 (32 bytes), the message of decapsulation
at 1248 (32 bytes), and its key `K̄` at 1280 (32 bytes); the working space
of the primitives at 2048 (2048 bytes); and polynomials of 1024 bytes from
4096 (`P k`), where each parameter set places the matrix, the outputs of
`PRF₂` and the working space of their computation (`Kem`).
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-! ## The layout of the working space -/

def oSV : Nat := 840
def oNB : Nat := 896
def oSB : Nat := 904
def oG : Nat := 1024
def oH : Nat := 1088
def oM : Nat := 1248
def oKB : Nat := 1280
def oSS : Nat := 2048
/-- Polynomial `k`. -/
def oP (k : Nat) : Nat := 4096 + 1024 * k

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.rbx, off)

/-! ## Moves -/

/-- `d ← p.1 + p.2`. -/
def lea (d : Reg) (p : Ptr) : List Instr := [.mov d (.reg p.1), .alu .add d (.imm (BitVec.ofNat 32 p.2))]

/-- The byte `v` to `p`. -/
def setB (p : Ptr) (v : Nat) : List Instr := [.mov32 .rax (.imm (BitVec.ofNat 32 v)), .store8 (at_ p.1 p.2) .rax]

/-- Copy `n` bytes (a multiple of 8) from `src` to `dst`, eight at a time. -/
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (lea .rdi dst ++ lea .rsi src ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 (n / 8)))]))
    (.loop (.block [.mov .rax (.mem (at_ .rsi 0)), .store (at_ .rdi 0) .rax, .alu .add .rdi (.imm 8),
      .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]) .ne)

/-! ## The sponge -/

/-- Zero the Keccak state. -/
def kzero : List Instr := .mov32 .rax (.imm 0) :: zeroSt .rbx 0

/-- Absorb the `len` bytes at `src`, at position `pos` of the block of `rate` bytes. -/
def kabs (src : Ptr) (len rate pos : Nat) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm (BitVec.ofNat 32 pos))] ++
      lea .rcx src ++ [.mov32 .r8 (.imm (BitVec.ofNat 32 len))] ++ lea .r9 (sc 200)))
    (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb)

/-- Pad, at position `pos`, with the suffix `suffix`. -/
def kpad (rate pos suffix : Nat) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm (BitVec.ofNat 32 pos)),
      .mov32 .rcx (.imm (BitVec.ofNat 32 suffix))] ++ lea .r8 (sc 200)))
    (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad)

/-- Squeeze `len` bytes from position 0 to `dst`. -/
def ksqz (rate : Nat) (dst : Ptr) (len : Nat) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm 0)] ++
      lea .rcx dst ++ [.mov32 .r8 (.imm (BitVec.ofNat 32 len))] ++ lea .r9 (sc 200)))
    (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze)

/-- Absorb the pieces `ps`, from position `pos` of the block. -/
def absAll (rate : Nat) : List (Ptr × Nat) → Nat → Prog isa
  | [], _ => .block []
  | (p, l) :: ps, pos => .seq (kabs p l rate pos) (absAll rate ps ((pos + l) % rate))

/-- The total length of the pieces. -/
def totLen (ps : List (Ptr × Nat)) : Nat := (ps.map (·.2)).sum

/-- A SHA-3 function or SHAKE (of rate `rate`, with the suffix `suffix`) of
the concatenation of the pieces `ps`, `len` bytes of it to `out`. -/
def hashAt (ps : List (Ptr × Nat)) (rate suffix : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  .seq (.block kzero) (.seq (absAll rate ps 0) (.seq (kpad rate (totLen ps % rate) suffix) (ksqz rate out len)))

/-! ## The polynomial primitives -/

/-- Which implementations of `vg_mlkem_compress_encode` and
`vg_mlkem_decode_decompress` a function calls: the baseline ones, or those
with AVX2. -/
inductive Codecs | base | avx2

def Codecs.ceN : Codecs → String
  | .base => "vg_mlkem_compress_encode"
  | .avx2 => "vg_mlkem_compress_encode_avx2"

def Codecs.ce : Codecs → Prog isa
  | .base => compressEncode
  | .avx2 => compressEncodeAvx2

def Codecs.ddN : Codecs → String
  | .base => "vg_mlkem_decode_decompress"
  | .avx2 => "vg_mlkem_decode_decompress_avx2"

def Codecs.dd : Codecs → Prog isa
  | .base => decodeDecompress
  | .avx2 => decodeDecompressAvx2

/-- The implementations (symbols and code) of the polynomial primitives that
both the top-level functions and the K-PKE functions use: `vg_mlkem_add`,
`vg_mlkem_sub`, `vg_mlkem_decode12` and `vg_mlkem_encode12`, and the
compression and decompression that go with them; the baseline ones (`sse`),
or those with AVX2 (`avx2`), which the K-PKE functions inline. -/
structure Prims where
  addN : String
  add : Prog isa
  subN : String
  sub : Prog isa
  dec12N : String
  dec12 : Prog isa
  enc12N : String
  enc12 : Prog isa
  codecs : Codecs

def Prims.sse : Prims :=
  ⟨"vg_mlkem_add", X86_64.add, "vg_mlkem_sub", X86_64.sub, "vg_mlkem_decode12", decode12,
    "vg_mlkem_encode12", encode12, .base⟩

def Prims.avx2 : Prims :=
  ⟨"vg_mlkem_add_avx2", addAvx2, "vg_mlkem_sub_avx2", subAvx2, "vg_mlkem_decode12_avx2", decode12Avx2,
    "vg_mlkem_encode12_avx2", encode12Avx2, .avx2⟩

/-- The polynomial arithmetic a top-level function with polynomials of `u32`s
calls: its primitives, `vg_mlkem_inv_ntt`, `vg_mlkem_cbd2`, the code the
products of K-PKE inline (`bodies`), and the products of encryption and
decryption (`encMul`, `decMul`); and `vg_mlkem16_cbd2`, which a top-level
function with 16-bit polynomials calls. -/
structure Arith extends Prims where
  nttInvN : String
  nttInv : Prog isa
  cbdN : String
  cbd : Prog isa
  /-- `cbd` with 16-bit coefficients (`vg_mlkem16_cbd2`). -/
  cbd16N : String
  cbd16 : Prog isa
  /-- The code `vg_mlkem*_{keygen,encrypt,decrypt}_mul` inline, and the suffix of their names. -/
  bodies : Bodies
  sfx : String
  /-- `vg_mlkem*_encrypt_mul` and `vg_mlkem*_decrypt_mul` of rank `k`. -/
  encMul : Nat → Prog isa
  decMul : Nat → Prog isa

/-- The baseline: SSE2. -/
def Arith.sse : Arith where
  toPrims := .sse
  nttInvN := "vg_mlkem_inv_ntt"
  nttInv := X86_64.nttInv
  cbdN := "vg_mlkem_cbd2"
  cbd := cbd2
  cbd16N := "vg_mlkem16_cbd2"
  cbd16 := cbd2_16
  bodies := .sse
  sfx := ""
  encMul := encryptMul .sse
  decMul := decryptMul .sse

/-- The baseline, but for `vg_mlkem16_cbd2_avx2`: what the implementations
with AVX2 call, whose top-level functions run with 16-bit polynomials. -/
def Arith.sse16 : Arith := { Arith.sse with cbd16N := "vg_mlkem16_cbd2_avx2", cbd16 := cbd2_16Avx2 }

def addAt (A : Arith) (f g : Ptr) : Prog isa := .seq (.block (lea .rdi f ++ lea .rsi g)) (.call A.addN A.add)

def subAt (A : Arith) (f g : Ptr) : Prog isa := .seq (.block (lea .rdi f ++ lea .rsi g)) (.call A.subN A.sub)

def cbd2At (A : Arith) (b f : Ptr) : Prog isa := .seq (.block (lea .rdi b ++ lea .rsi f)) (.call A.cbdN A.cbd)

def enc12At (A : Arith) (f out : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ lea .rsi out)) (.call A.enc12N A.enc12)

def dec12At (A : Arith) (b f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi b ++ lea .rsi f)) (.call A.dec12N A.dec12)

/-- A call of the compression `n` (code `c`, with the signature of
`vg_mlkem_compress_encode`) of `f` to width `d`, to `out`. -/
def ceCall (n : String) (c : Prog isa) (f : Ptr) (d : Nat) (out : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 d))] ++ lea .rdx out ++
      [.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * d)))]))
    (.call n c)

/-- A call of the decompression `n` (code `c`, with the signature of
`vg_mlkem_decode_decompress`) of the `32d` bytes at `b` to `f`. -/
def ddCall (n : String) (c : Prog isa) (b : Ptr) (d : Nat) (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi b ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))), .mov32 .rdx (.imm (BitVec.ofNat 32 d))] ++
      lea .rcx f))
    (.call n c)

/-- A call of the compression of `cs`. -/
abbrev ceAt (cs : Codecs) : Ptr → Nat → Ptr → Prog isa := ceCall cs.ceN cs.ce

/-- A call of the decompression of `cs`. -/
abbrev ddAt (cs : Codecs) : Ptr → Nat → Ptr → Prog isa := ddCall cs.ddN cs.dd

/-- `SampleNTT` of the seed at `SB` to `a`, and `r15 ← r15 ∧ result`. -/
def sampleAt (a : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc oSB) ++ lea .rsi a ++ lea .rdx (sc oSS)))
    (.seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.alu32 .and .r15 (.reg .rax)]))

/-! ## The matrix and the other polynomials -/

/-- Polynomial `k` of the working space. -/
abbrev pS (k : Nat) : Ptr := sc (oP k)

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` to `a`, with `ρ` at `SB`. -/
def sampleIJ (a : Ptr) (i j : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) (sampleAt a)

/-- Seed `k` of four, `ρ ‖ j ‖ i` with `ρ` at `SB`, to `34 k` bytes into `scratch`. -/
def seedAt (k i j : Nat) : Prog isa :=
  .seq (copy (sc (34 * k)) (sc oSB) 32) (.block (setB (sc (34 * k + 32)) j ++ setB (sc (34 * k + 33)) i))

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## `PRF₂`, several at once -/

/-- `σ` (or `r`): the second half of `G`'s output. -/
abbrev sigP : Ptr := sc (oG + 32)

/-- `PRF₂(σ, N)` (128 bytes) to `out`, with `σ` at `G + 32`. -/
def prf1 (N : Nat) (out : Ptr) : Prog isa :=
  .seq (.block (setB (sc oNB) N)) (hashAt [(sigP, 32), (sc oNB, 1)] 136 0x1f out 128)

/-- `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, one at a
time (the working space at lane `wl` is not used). -/
def prfsScalar (N₀ n o _wl : Nat) : Prog isa := seqR (fun i => prf1 (N₀ + i) (sc (o + 128 * i))) 0 n

namespace Prf4

open VG.Impl.Sha3.X86_64.X4 (vb st permute4 rcTable)

/-! Four instances of `PRF₂` at once, in the four 64-bit elements of `ymm`
registers (`Impl/Sha3/X86_64/X4.lean`), in 2368 bytes of working space
from lane `wl` of `scratch` (byte `32 wl`): the four states (interleaved,
800 bytes), the second buffer of the permutation (800 bytes) and the table
of the round constants (768 bytes). The input `σ ‖ N` is 33 bytes, and the
128 bytes of output fewer than the rate of SHAKE256 (136), so the padded
input is one block and the output its permutation's first 128 bytes. -/

/-- The four states, zeroed. -/
def zero (wl : Nat) : List Instr :=
  vb .vpxor .xmm0 .xmm0 .xmm0 :: (List.range 25).flatMap fun i => [st .rbx (wl + i) .xmm0]

/-- Lanes 0–3 of each state: the 32 bytes of `σ`. -/
def sigLanes (wl : Nat) : List Instr :=
  (List.range 4).flatMap fun i => .mov .rax (.mem (at_ .rbx (oG + 32 + 8 * i))) ::
    (List.range 4).flatMap fun k => [.store (at_ .rbx (32 * (wl + i) + 8 * k)) .rax]

/-- Byte 32 of state `k`: the index `N₀ + k`, for `N₀` in `r9`. -/
def nonces (wl : Nat) : List Instr :=
  .mov .rax (.reg .r9) :: (List.range 4).flatMap fun k =>
    [.store8 (at_ .rbx (32 * (wl + 4) + 8 * k)) .rax, .alu .add .rax (.imm 1)]

/-- SHAKE's suffix `0x1f` at byte 33 of each state, and the last bit of the
padding (`0x80`) at byte 135. -/
def pads (wl : Nat) : List Instr :=
  .mov32 .rax (.imm 0x1f) :: ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (wl + 4) + 8 * k + 1)) .rax]) ++
    .mov32 .rax (.imm 0x80) :: (List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (wl + 16) + 8 * k + 7)) .rax]

/-- The arguments of `permute4`. -/
def args (wl : Nat) : List Instr :=
  [.mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 (32 * wl))), .mov .rsi (.reg .rbx),
    .alu .add .rsi (.imm (BitVec.ofNat 32 (32 * (wl + 25)))), .mov .rdx (.reg .rbx),
    .alu .add .rdx (.imm (BitVec.ofNat 32 (32 * (wl + 50)))), .mov .rcx (.reg .rbx),
    .alu .add .rcx (.imm (BitVec.ofNat 32 (32 * (wl + 74))))]

/-- The first 128 bytes of states `0, …, m - 1` to `r8 + 128 k`. -/
def extract (m wl : Nat) : List Instr :=
  (List.range m).flatMap fun k => (List.range 16).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (32 * (wl + i) + 8 * k))), .store (at_ .r8 (128 * k + 8 * i)) .rax]

/-- The table, the padded inputs and the arguments of the permutation. -/
def setup (wl : Nat) : List Instr :=
  rcTable .rbx (wl + 50) ++ zero wl ++ sigLanes wl ++ nonces wl ++ pads wl ++ args wl

/-- `PRF₂(σ, N₀ + k)` to `r8 + 128 k` for each `k < m` (at most four), at
once, for `N₀` in `r9` (the permutation keeps `r8`–`r10`). After the
copies, `vzeroupper` clears the upper halves of the vector registers, so
that the SSE code that runs next does not pay for mixing them. -/
def batch (m wl : Nat) (fast : Bool := false) : Prog isa :=
  .seq (.block (setup wl)) (.seq (permute4 fast) (.block (extract m wl ++ [.vop .vzeroupper])))

/-- `r8 := scratch + o` and `r9 := N₀`. -/
def regs (N₀ o : Nat) : List Instr :=
  [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 o)), .mov32 .r9 (.imm (BitVec.ofNat 32 N₀))]

/-- The next four: `r8 += 512`, `r9 += 4`, `r10 -= 1` (ZF set at 0). -/
def next : List Instr := [.alu .add .r8 (.imm 512), .alu .add .r9 (.imm 4), .alu .sub .r10 (.imm 1)]

/-- `q` batches of four from `N₀` (`q ≥ 1`), to `scratch + o + 512 i`, in a
loop, which leaves `r8` and `r9` at the next. -/
def quads (N₀ q o wl : Nat) (fast : Bool := false) : Prog isa :=
  .seq (.block (regs N₀ o ++ [.mov32 .r10 (.imm (BitVec.ofNat 32 q))]))
    (.loop (.seq (batch 4 wl fast) (.block next)) .ne)

end Prf4

/-- `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, four at a
time: the batches of four in a loop (`quads`), then the last `n mod 4`
with lanes whose outputs are not copied. -/
def prfsX4 (fast : Bool := false) (N₀ n o wl : Nat) : Prog isa :=
  .seq (if n / 4 = 0 then .block [] else Prf4.quads N₀ (n / 4) o wl fast)
    (if n % 4 = 0 then .block []
      else .seq (.block (Prf4.regs (N₀ + 4 * (n / 4)) (o + 512 * (n / 4)))) (Prf4.batch (n % 4) wl fast))

/-- How many of `n` outputs `prfsAvx2` computes one at a time, first:
`n mod 4` when it is 1 or 2. (Four instances at once cost about as much as
two on their own, so this is as fast as running them with lanes whose
outputs are not copied, and the code is shorter; three are four at a time.) -/
def prfsLead (n : Nat) : Nat := if n % 4 = 1 ∨ n % 4 = 2 then n % 4 else 0

/-- `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, with AVX2:
the first `prfsLead n` one at a time, and the others four at a time. -/
def prfsAvx2 (N₀ n o wl : Nat) (fast : Bool := false) : Prog isa :=
  .seq (prfsScalar N₀ (prfsLead n) o wl) (prfsX4 fast (N₀ + prfsLead n) (n - prfsLead n) (o + 128 * prfsLead n) wl)

/-- An implementation of `vg_mlkem_sample_ntt4` to call (its symbol and its
code), and of the computation of several outputs of `PRF₂` that goes with
it, which its callers inline: `prfs N₀ n o wl` writes `PRF₂(σ, N₀ + i)`
(with `σ` at `G + 32`) to `scratch + o + 128 i` for each `i < n`, with the
working space from lane `wl` of `scratch`. The top-level functions, which
use both, are emitted once for each (`Generic/MlKemSample4/X86_64/`). -/
structure Callee4 where
  name : String
  code : Prog isa
  prfs : Nat → Nat → Nat → Nat → Prog isa
  /-- The polynomial arithmetic that goes with it. -/
  arith : Arith
  /-- The symbol and code of the same implementation with 16-bit
  coefficients, if it has one. -/
  s16 : Option (String × Prog isa)
  /-- The fragment encapsulation inlines to sample three entries of the
  matrix with 16-bit coefficients while absorbing three blocks of `ek`
  into `H`'s sponge (`Sample4.sampleH fast true`), if the implementation
  has one. -/
  batchH16 : Option (Prog isa)
  /-- The fragment key generation inlines to sample three entries of the
  matrix with 16-bit coefficients while absorbing the first `m` of three
  blocks of `ek` into `H`'s sponge (`Sample4.sampleHM fast m`), if the
  implementation has one. -/
  batchHM16 : Option (Nat → Prog isa)
  /-- The fragment key generation and encapsulation inline to sample three
  entries of the matrix with 16-bit coefficients while computing
  `PRF₂(σ, N₀)`, …, `PRF₂(σ, N₀ + m - 1)` for `m ≤ 3`
  (`Sample4.samplePN fast N₀ m`), if the implementation has one. -/
  batchP16 : Option (Nat → Nat → Prog isa)

def Callee4.scalar : Callee4 := ⟨"vg_mlkem_sample_ntt4", Sample4.sampleNTT4, prfsScalar, .sse, none,
  none, none, none⟩
/-- Four-way sampling with AVX2, with 16-bit coefficients; the functions of
`u32`s, which callers run only without `s16`, are the baseline's sampler. -/
def Callee4.avx2 : Callee4 :=
  ⟨"vg_mlkem_sample_ntt4", Sample4.sampleNTT4, (fun n k o w => prfsAvx2 n k o w), .sse16,
    some ("vg_mlkem16_sample_ntt4_avx2", Sample4.sampleNTT4Avx2 false true),
    some (Sample4.sampleH false true), some (Sample4.sampleHM false), some (Sample4.samplePN false)⟩

/-- Four-way sampling with AVX-512VL quadword rotates. -/
def Callee4.avx512 : Callee4 :=
  ⟨"vg_mlkem_sample_ntt4", Sample4.sampleNTT4, (fun n k o w => prfsAvx2 n k o w true), .sse16,
    some ("vg_mlkem16_sample_ntt4_avx512", Sample4.sampleNTT4Avx2 true true),
    some (Sample4.sampleH true true), some (Sample4.sampleHM true), some (Sample4.samplePN true)⟩

/-- `SampleNTT` of the four seeds at `scratch` to the four polynomials from
`a`, with the working space `scr` (8192 bytes), and `r15 ← r15 ∧ result`. -/
def sample4At (c : Callee4) (a scr : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ lea .rsi a ++ lea .rdx scr))
    (.seq (.call c.name c.code) (.block [.alu32 .and .r15 (.reg .rax)]))

/-- Entries `e₀, …, e₀ + 3` of a matrix of `n` columns (entry `e = n i + j`),
from polynomial `a`, with `SampleNTT` on the four seeds at once. -/
def quad (c : Callee4) (n e₀ : Nat) (a scr : Ptr) : Prog isa :=
  .seq (seedAt 0 (e₀ / n) (e₀ % n)) (.seq (seedAt 1 ((e₀ + 1) / n) ((e₀ + 1) % n))
    (.seq (seedAt 2 ((e₀ + 2) / n) ((e₀ + 2) % n)) (.seq (seedAt 3 ((e₀ + 3) / n) ((e₀ + 3) % n))
      (sample4At c a scr))))

/-- `c` if every `SampleNTT` so far succeeded (`r15 ≠ 0`). -/
def ifOk (c : Prog isa) : Prog isa :=
  .seq (.block [.alu32 .test .r15 (.reg .r15)]) (.ite .ne c (.block []))

/-! ## Entry and exit -/

/-- The callee-saved registers the top-level functions save, at `scratch + 840 + 8k`. -/
def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Save the callee-saved registers in the working space at `scr`, keep `scr`
in `rbx` and the pointers in the other registers (`moves`), and `r15 ← 1`. -/
def topPro (scr : Reg) (moves : List (Reg × Reg)) : List Instr :=
  (List.range 6).map (fun k => .store (at_ scr (oSV + 8 * k)) (savedRegs.getD k .rbx)) ++
    [.mov .rbx (.reg scr)] ++ moves.map (fun m => .mov m.1 (.reg m.2)) ++ [.mov32 .r15 (.imm 1)]

/-- Return `r15`, and restore the callee-saved registers (`rbx` last). -/
def topEpi : List Instr :=
  .mov32 .rax (.reg .r15) ::
    ((List.range 5).map fun k => .mov (savedRegs.getD (5 - k) .rbx) (.mem (at_ .rbx (oSV + 8 * (5 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSV))]

end VG.Impl.MlKem.X86_64
