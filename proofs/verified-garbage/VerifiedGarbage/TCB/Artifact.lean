module

public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Sig

/-!
# Targets, contracts and verified artifacts

**Trusted.** This file defines what it *means* for an emitted function to be
verified. Every function the Rust crate contains is an `Artifact`
(`TCB/Registration.lean`, with the printer of its target), and an
`Artifact` cannot be constructed without a proof of `Verified`.

`Verified T c k` says, for the machine code `c` on target `T` and contract `k`:

1. **Total correctness and memory safety.** From every state satisfying
   `k.pre`, `c` terminates without faulting (so every memory access stays in
   the regions the state permits) in a state related to the initial one by
   `k.post` *and* by the target's calling-convention obligations
   `T.abiPreserved` (callee-saved registers, stack pointer, return address).
2. **Constant time.** Any two runs from `k.pre`-states that agree on public
   data (`k.pub`) have identical leakage traces (addresses and branches).
   Public data is the pointers, lengths and public integer arguments, plus
   anything the contract declares the function may leak (`Sig.contract`'s
   `leak`): the traces may depend on that, and on nothing else secret.
3. **Non-vacuity.** Some state satisfies `k.pre`. This is only a sanity
   check against an accidentally contradictory precondition; it does not
   replace reviewing the contract.

What a reviewer must read for each artifact is therefore: the ISA model and
ABI of its target (`TCB/<arch>/`), its contract (in `Spec/`), and its Rust
signature (`Sig`) and documentation (its `Api` in `Spec/`, and what its
registration file adds for the target). The code and the proof need not be
read.
-/

@[expose] public section

namespace VG

/-- The specification of one function. -/
structure Contract (M : ISA) where
  /-- Precondition on the entry state: argument registers, permitted memory
  regions, disjointness, CPU features, … -/
  pre : M.State → Prop
  /-- Postcondition relating the entry state to the exit state. -/
  post : M.State → M.State → Prop
  /-- When two entry states agree on everything public (e.g. lengths and
  pointers, but not keys or plaintexts). -/
  pub : M.State → M.State → Prop

/-- A code-generation target: an ISA model and its calling convention. What
only the emitter reads of it (its printer, its Rust `cfg` and ABI string, and
how documentation names its argument area and reserved memory: `Emitter`,
`EmitTarget`) is not part of it: every proof imports `Target`, and none
depends on how its code is printed or documented. -/
structure Target where
  /-- Short name; also the name of the generated Rust module (e.g. `x86_64`). -/
  name : String
  isa : ISA
  /-- Calling-convention obligations every function must meet when it
  returns, relating the entry state to the exit state (callee-saved
  registers and the stack pointer restored, return address intact). -/
  abiPreserved : isa.State → isa.State → Prop
  /-- The calling convention, which the target's Rust ABI string stands for
  (`Emitter.rustAbi`). -/
  abi : Abi isa
  /-- What it means on this target for a function with code `c`, contract
  `k` and a result of `retBits` bits to return without secret residue
  (`X86_64.NoResidue`), if the target defines it: then every artifact of the
  target proves it (`Artifact.residue`), but those `ci/residue_allowlist.txt`
  lists, as the emitter checks (`Rust.checkResidue`). -/
  noResidue : Option (Prog isa → Contract isa → Nat → Prop) := none

/-- The contract of a function with signature `sig` under the calling
convention `A`: the obligations the signature implies (see `TCB/Sig.lean`),
the further precondition `pre` and the postcondition `post`, both stated on
the arguments by name. If `writeArgs`, the function may also overwrite its
arguments passed in memory, where the calling convention gives them to the
callee; otherwise it may only read them. `stack` is the number of bytes of
stack below the stack pointer that the function's calls and frames use
(return addresses, arguments and saved registers), which no buffer
overlaps. A calling convention that does not model the arguments (`A.args`
is `none`) gives an unsatisfiable precondition, which `Verified` rejects.
Only the bits of a public argument's own width are public: a 32-bit argument
in a 64-bit register leaves the upper half unspecified (whatever the caller
left there, which may be secret), so two runs need not agree on it.

A list of slices (`Param.slices`) adds read-only memory that depends on the
memory on entry: its descriptors, and the slices they list (`Sig.lists`),
which may overlap each other and the other read-only buffers, but no
writable buffer (a `&[&[T]]` and a `&mut` are distinct Rust objects). What
its descriptors say is public (`Sig.descs`): two runs agree on their bytes.
A table of functions (`Param.table`) adds read-only memory too: its words,
of the target's pointer width (`Sig.lists`); `Abi.withTables` says what they
hold.

`leak`, if given, declares what the function may leak beyond its public
arguments: a list of numbers computed from the arguments and the memory on
entry (e.g. the sequence of table indices an algorithm reads, when the
algorithm itself makes them depend on secrets). It is added to the public
data, so two runs need identical leakage traces only if they agree on it:
the function may reveal it through its timing, and nothing else secret.
Every contract without `leak` is constant time in the usual sense. -/
def Sig.contract {M : ISA} (A : Abi M) (sig : Sig)
    (pre : Curry (sig.words A.ptrBits) (Mem → Prop) := Curry.const (fun _ => True) _)
    (post : sig.Post A.ptrBits) (writeArgs : Bool := false) (stack : Nat := 0)
    (leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat)) := none) : Contract M :=
  let ws := sig.words A.ptrBits
  let widths := ws.map (·.bits A.ptrBits)
  let pubs := sig.params.flatMap (·.2.pubs)
  { pre s := match A.args widths with
      | none => False
      | some vals =>
        let bufs := Sig.bufs sig.params (vals s) ++
          (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)
        let all := bufs ++ (A.argArea widths s).map fun (r, w) => (r, w && writeArgs)
        A.wf widths stack s ∧
        A.rd s = (all.filter (!·.2)).map (·.1) ∧ A.wr s = (all.filter (·.2)).map (·.1) ∧
        all.Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
        (∀ r ∈ A.reserved stack s, ∀ a ∈ all, r.Disjoint a.1) ∧
        (∀ a ∈ bufs, a.1.base.toNat + a.1.len ≤ 2 ^ A.ptrBits) ∧
        bif A.alignsBufs then
          Curry.apply ws pre (vals s) (A.mem s) ∧
            ∀ p ∈ Sig.alignedBufs sig.params (vals s), p.1.toNat % p.2 = 0
        else Curry.apply ws pre (vals s) (A.mem s)
    post s s' := match A.args widths with
      | none => False
      | some vals => Curry.apply ws post (vals s) (A.mem s) (A.mem s')
          ((A.ret s').setWidth _)
    pub s₁ s₂ := match A.args widths with
      | none => False
      | some vals =>
        (match leak with
          | none => A.pub s₁ s₂
          | some f => A.pub s₁ s₂ ∧
            Curry.apply ws f (vals s₁) (A.mem s₁) = Curry.apply ws f (vals s₂) (A.mem s₂)) ∧
        (∀ i, pubs.getD i false = true →
          ((vals s₁).getD i 0).setWidth (widths.getD i 64) =
            ((vals s₂).getD i 0).setWidth (widths.getD i 64)) ∧
        ∀ r ∈ Sig.descs A.ptrBits sig.params (vals s₁), ∀ i < r.len,
          A.mem s₁ (r.base + BitVec.ofNat 64 i) = A.mem s₂ (r.base + BitVec.ofNat 64 i) }

/-- The proof obligation for emitting `c` on target `T` with contract `k`. -/
def Verified (T : Target) (c : Prog T.isa) (k : Contract T.isa) : Prop :=
  (∀ s, k.pre s → ∃ t s', Exec T.isa c s t s' ∧ T.abiPreserved s s' ∧ k.post s s') ∧
  ConstantTime T.isa k.pre k.pub c ∧
  (∃ s, k.pre s)

/-- A function's contract on every target: the contract under the calling
convention `A`, for an implementation whose calls and frames use `stack`
bytes of stack below the stack pointer (`Sig.contract`'s `stack`; a contract
that does not depend on it is the one with `stack` 0). -/
abbrev Contracts : Type 1 := {M : ISA} → Abi M → Nat → Contract M

/-- What a function is on every target: its Rust module, name and signature,
whether its contract lets it overwrite its arguments in memory
(`Sig.contract`'s `writeArgs`), its contract on every target (`contracts`),
and its documentation. A registration file makes an `Artifact` of it on each
target (`{ api with target := …, doc := api.doc, … }`); the emitter adds the
obligations the signature implies (`Sig.validDoc`, and `Sig.layoutDoc`,
which depends on the target).

The `Artifact` takes `contracts` from the `Api` with its name and signature,
and must be proven against `contracts` on its target (`Artifact.ofApi`): so
the Rust name, signature and documentation that `Spec/` gives a function are
those of the contract `Spec/` gives it, and nothing outside `Spec/` pairs
them. -/
structure Api where
  module : String
  name : String
  sig : Sig
  writeArgs : Bool := false
  /-- The function's contract on every target, `fun A stack => fooContract A
  stack`. The emitter refuses an artifact without one (`Rust.checkApi`). -/
  contracts : Option Contracts := none
  /-- Whether `contracts` make the mode public (`Abi.withMode`): only those
  of `Spec/Dit.lean`, whose functions set it. -/
  pubMode : Bool := false
  /-- The documentation, up to its `# Safety` section. -/
  summary : String
  /-- The items of the `# Safety` section, but for those `Sig.validDoc` and
  `Sig.layoutDoc` give (what memory each buffer must be valid for, and where
  it may be). -/
  safety : List String

end VG
