module

public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Print

/-!
# Registering an implementation of an `Api`

**Trusted.** A registration file makes each function's `Artifact` from its
`Api` with `Api.artifact`, stating only what the implementation chooses: the
target, the code and its proof, the stack it uses and the constant tables it
reads (which `stack_of` and `consts_of` find in the contract the proof is
of), the tables of functions it takes, how much
of its writable arrays it writes (`written`, with its proof), the proof that
it returns without secret residue (`residue`), and the suffix of its name. Everything else
comes from the `Api` (`Spec/`): the Rust module, name, signature and
documentation, `writeArgs`, and the contract on the target, which the proof
is of; or from the code: the CPU features it needs (`Code.requiresDedup`).
So of a registration, a reviewer reads `suffix`; the kernel checks
the rest, `written` included. The code is printed, and its documentation
written, with what the emitter needs of the target, its ISA's one `Emitter`
instance (`TCB/<ISA>/Print.lean`), which `Api.artifact` pairs with the target
(`EmitTarget`).

`Artifact`, `EmitTarget` and how the documentation states the obligations a
signature implies are defined here rather than with `Target` and `Verified`
(`TCB/Artifact.lean`), which every proof imports, so that no proof depends on
a printer or on the emitted documentation.
-/

@[expose] public section

namespace VG

/-- A target with what the emitter needs of it besides its model and calling
convention (its ISA's `Emitter`): the target an artifact is emitted for.
None of it is part of `Target`, which every proof imports, so that a change
to it rebuilds only the registration files and the emitter, not the proofs. -/
structure EmitTarget extends Target where
  printer : Printer isa
  /-- `Emitter.rustCfg`. -/
  rustCfg : String
  /-- `Emitter.rustAbi`. -/
  rustAbi : String
  /-- `Emitter.argAreaDoc`. -/
  argAreaDoc : List Nat → Option (String × Bool)
  /-- `Emitter.reservedDoc`. -/
  reservedDoc : Nat → Option String

/-- The target `T` with its ISA's `Emitter`. -/
def EmitTarget.of (T : Target) [e : Emitter T.isa] : EmitTarget :=
  ⟨T, e.printer, e.rustCfg, e.rustAbi, e.argAreaDoc, e.reservedDoc⟩

/-! ## Documenting the obligations `Sig.contract` implies

The emitter adds to each function's `# Safety` section what `Sig.contract`
requires of the memory each buffer is valid for (`Sig.validDoc`) and of where
its buffers are (`Sig.layoutDoc`), and a note if it may overwrite its
arguments (`Sig.layoutNote`), from the same signature, calling convention,
`writeArgs` and `stack` as its contract (`Artifact.ofSig`). The
target's `Emitter` names its calling convention's argument area and reserved
memory (`EmitTarget.argAreaDoc`, `EmitTarget.reservedDoc`).
-/

/-- The buffers of the parameters `ps` as the documentation names them, and
whether each is writable: those of `Sig.bufs`, in the same order, each list
of slices followed by the slices it lists (`Sig.lists`). -/
def Sig.bufNames : List (String × Param) → List (String × Bool)
  | [] => []
  | (_, .int ..) :: ps => Sig.bufNames ps
  | (n, .array w ..) :: ps => (s!"`{n}`", w) :: Sig.bufNames ps
  | (n, .slice w ..) :: ps => (s!"`{n}`", w) :: Sig.bufNames ps
  | (n, .slices ..) :: ps => (s!"`{n}`", false) :: (s!"the slices `{n}` lists", false) :: Sig.bufNames ps
  | (n, .table _) :: ps => (s!"`{n}`", false) :: Sig.bufNames ps

/-- The size in bytes of the buffer a parameter stands for, as the
documentation states it: that of `Sig.bufs`, a number for an array and
`` `len` `` or `` `k * len` `` for a slice of `len` elements of `k` bytes, and
`` `2 * size_of::<usize>() * count` `` for the descriptors of a list of `count` slices,
`` `n * size_of::<usize>()` `` for a table of `n` words;
`none` for an integer. -/
def Param.sizeDoc : Param → Option String
  | .int .. => none
  | .array _ e n => some s!"{n * e.size}"
  | .slice _ e len => some (if e.size = 1 then s!"`{len}`" else s!"`{e.size} * {len}`")
  | .slices _ count => some s!"`2 * size_of::<usize>() * {count}`"
  | .table n => some s!"`{n} * size_of::<usize>()`"

/-- The `# Safety` items stating the memory each buffer of `sig` must be
valid for, in order: the region `Sig.contract` lets the function read
(every buffer; loads may read the writable regions too) and write (the
writable buffers), of the size `Sig.bufs` gives it, and, on a target whose
contracts require it (`Abi.alignsBufs`), that a buffer of `u16`, `u32` or
`u64` (`Sig.alignedBufs`) is aligned for its element. -/
def Sig.validDoc {M : ISA} (A : Abi M) (sig : Sig) : List String :=
  sig.params.filterMap fun (n, p) =>
    let access := match p with
      | .array true .. | .slice true .. => "reads and writes"
      | _ => "reads"
    let listed := match p with
      | .slices e _ => if e.size = 1 then s!", and each slice it lists for reads of its length in \
          bytes" else s!", and each slice it lists for reads of {e.size} times its length in bytes"
      | _ => ""
    let aligned := match p with
      | .array _ e _ | .slice _ e _ =>
        if A.alignsBufs && 1 < e.align then s!", and aligned for `{e.scalar.rust}`" else ""
      | _ => ""
    p.sizeDoc.map fun size =>
      s!"`{n}` must be valid for {access} of {size} bytes{listed}{aligned}."

/-- `xs` as an English list joined by `conj`: "a", "a or b", "a, b or c". -/
def englishList (conj : String) : List String → String
  | [] => ""
  | [x] => x
  | [x, y] => s!"{x} {conj} {y}"
  | x :: xs => s!"{x}, " ++ englishList conj xs

/-- The `# Safety` items stating what the contracts `sig.contract T.abi _ _
writeArgs stack _` require of where the buffers are: that a writable buffer
overlaps no other buffer, nor the arguments in memory (`T.abi.argArea`); that no
buffer overlaps the arguments in memory if the function may write them, nor
the memory `T.abi.reserved stack` (the return address, and the stack that the
function's calls and frames use); and that no buffer wraps around the end of
the address space. -/
def Sig.layoutDoc (T : EmitTarget) (sig : Sig) (writeArgs : Bool) (stack : Nat) :
    List String :=
  let bufs := Sig.bufNames sig.params
  let all := bufs.map (·.1)
  let w := (bufs.filter (·.2)).map (·.1)
  let r := (bufs.filter (!·.2)).map (·.1)
  let args := T.argAreaDoc ((sig.words T.abi.ptrBits).map (·.bits T.abi.ptrBits))
  let argsWritable := match args with
    | some (_, wr) => wr && writeArgs
    | none => false
  let argsName := (args.map (·.1)).toList
  let wObjs := (if w.length ≥ 2 then ["each other"] else []) ++ r ++
    (if argsWritable then [] else argsName)
  let allObjs := (if argsWritable then argsName else []) ++ (T.reservedDoc stack).toList
  let tail := ", ".intercalate (allObjs.map ("overlap " ++ ·)) ++
    (if allObjs.isEmpty then "" else ", or ") ++ "wrap around the end of the address space"
  (if w.isEmpty || wObjs.isEmpty then [] else
    [s!"{englishList "and" w} must not overlap {englishList "or" wObjs} (distinct Rust \
      objects never do)."]) ++
  match all with
    | [] => []
    | [b] => [s!"{b} must not {tail} (no Rust object does)."]
    | [a, b] => [s!"Neither {a} nor {b} may {tail} (no Rust object does)."]
    | _ => [s!"None of {englishList "and" all} may {tail} (no Rust object does)."]

/-- A paragraph saying that the function may overwrite its arguments in
memory, if the contracts `sig.contract T.abi _ _ writeArgs _ _` let it. -/
def Sig.layoutNote (T : EmitTarget) (sig : Sig) (writeArgs : Bool) : List String :=
  match T.argAreaDoc ((sig.words T.abi.ptrBits).map (·.bits T.abi.ptrBits)) with
  | some (d, true) => if writeArgs then
      [s!"The function may overwrite {d}, as the calling convention lets it."] else []
  | _ => []

/-- The documentation of `api` on a target: its summary, then its `# Safety`
section. -/
def Api.doc (api : Api) : String :=
  api.summary ++ "\n\n# Safety\n\n" ++
    "\n".intercalate (api.safety.map ("* " ++ ·))

/-- A verified function, ready to be emitted into the Rust crate. -/
structure Artifact where
  target : EmitTarget
  /-- The Rust module the function is emitted into, `src/asm/<target>/<module>.rs`
  (e.g. `sha256`). -/
  module : String
  /-- The Rust function name. Must be unique within the target. -/
  name : String
  /-- The name of the function it implements, its `Api`'s (`Api.artifact`),
  which `name` extends with the implementation's suffix: the artifacts of a
  target with the same `base` are the implementations of one function, which
  its dispatcher may call in each other's place (`Rust.groupsOf`). By
  default, its own name: an artifact not made from an `Api` is the only
  implementation of its function. -/
  base : String := name
  /-- The Rust signature, rendered as the parameter list and return type
  (`Sig.rust`). -/
  sig : Sig
  /-- Documentation for the generated Rust function. With what the emitter
  adds to it (`Sig.layoutNote`, `Sig.validDoc` and `Sig.layoutDoc`, which
  need it to end with its `# Safety` section if they add anything, and not
  to state what they do), it must state every
  requirement of `contract.pre` that the caller is responsible for, and
  anything the contract declares the function may leak (`Sig.contract`'s
  `leak`). -/
  doc : String
  /-- Tables of 64-bit constants the code reads, by name: the emitter writes
  each as a `static` of that name, from which the code forms the table's
  address (`Abi.sym`; on AArch64, ARMv7 and PPC64LE, `adrSym`; on RISC-V,
  `lla`; on x86-64, `leaSym`), and checks that every artifact of the target with a table of that name gives
  the same words (`Rust.checkConsts`). So `contract` is one for the calling convention
  `target.abi.withConsts consts` (`Abi.withConsts`). A table an instruction
  carries (x86-64's `aluTbl`, `Printer.tables`) is written and checked the
  same way without being listed here: the model reads its words from the
  instruction, not from memory the contract describes. -/
  consts : List (String × List (BitVec 64)) := []
  /-- The tables of functions the function takes (`Abi.withTables`): for
  each of its parameters that is one, the parameter's name and every table
  it may point to. The emitter checks that each names a read-only array of
  `u64` of the tables' length, and that it lists every table of their
  interface on the target, of which the Rust caller may pass any
  (`Rust.checkFnTables`). So `contract` is one for the calling convention
  `(target.abi.withConsts consts).withTables sig tables`. -/
  tables : List (String × List FnTable) := []
  code : Prog target.isa
  contract : Contract target.isa
  verified : Verified target.toTarget code contract
  /-- `Sig.contract`'s `writeArgs` and `stack` for `contract` (see `ofSig`). -/
  writeArgs : Bool := false
  stack : Nat := 0
  /-- Whether `contract` makes the mode public (`Abi.withMode`, see `ofSig`). -/
  pubMode : Bool := false
  /-- `contract` is one that `Sig.contract` derives from `sig` for the
  target's calling convention, `writeArgs` and `stack`: so it reads the
  arguments and writes the return value where the calling convention places
  them for `sig`, and requires what `Sig.layoutDoc` documents of where the
  buffers are. -/
  ofSig : ∃ pre post leak,
      contract = sig.contract (((target.abi.withConsts consts).withTables sig tables).withMode pubMode)
        pre post writeArgs stack leak := by
    exact ⟨_, _, _, rfl⟩
  /-- The contract of the function on every target, which an artifact made
  from an `Api` (`{ api with … }`) takes from it with its `name` and `sig`
  (`Api.contracts`). The emitter refuses an artifact without one
  (`Rust.checkApi`). -/
  contracts : Option Contracts := none
  /-- `contract` is `contracts` on the target, for `stack`: an artifact made
  from an `Api` is proven against the contract `Spec/` gives the function,
  not one chosen where the artifact is built. -/
  ofApi : contracts.elim True fun f =>
      contract = f ((target.abi.withConsts consts).withTables sig tables) stack := by
    first | exact True.intro | exact rfl
  /-- The code changes the stack pointer only by calls and returns and by
  the pushes and pops of frames, which are nested: no other instruction of
  it, or of the functions it calls, writes it. So a call instruction or a
  push only ever stores below the stack pointer on entry, where no Rust
  object lies. -/
  spSafe : code.all (fun i => !target.isa.writesSp i) = true := by decide +kernel
  /-- The CPU features beyond the target's baseline ISA that the code needs,
  by their Rust `target_feature` names: exactly those its instructions, and
  those of the functions it calls, require (`ISA.requires`). The emitter
  checks this (`Rust.checkFeatures`) and adds their presence to the
  function's `# Safety` section, which `doc` must end with when this is not
  empty. -/
  features : List String := []
  /-- How much of some writable array parameters the function writes, in
  bytes: for each `(name, n)`, it changes no byte of the buffer of the
  parameter `name` at offset `n` or beyond (`writtenOk`). The emitter checks
  that each names a writable array parameter, once, with `n` at most its size
  (`Rust.checkWritten`), exports `n` as the constant
  `<NAME>_<PARAM>_WRITTEN` (`Rust.writtenConsts`) and documents it, so that a
  caller that must destroy what the function wrote there need destroy only
  the first `n` bytes. -/
  written : List (String × Nat) := []
  /-- Every run from a state satisfying `contract.pre` changes no byte of
  those buffers beyond their bounds (`Sig.writtenWithin`), which are where
  the target's calling convention places the arguments: `Sig.writtenWithin`
  reads only its `args`, `ptrBits` and `mem`, which the tables of constants
  (`Abi.withConsts`) and of functions (`Abi.withTables`) leave as they are. -/
  writtenOk : ∀ s t s', contract.pre s → Exec target.isa code s t s' →
      Sig.writtenWithin target.abi sig written s s' := by
    exact fun _ _ _ _ _ => True.intro
  /-- CPU features beyond `features`, by their Rust `target_feature` names,
  without which its function's dispatcher does not choose it: those of the
  CPUs it is faster on. -/
  extra : List String := []
  /-- The compilation target's `target_vendor`, if any, outside which its
  function's dispatcher chooses it only where `VG_CPU_FEATURES` names every
  feature it needs: that of the CPUs it is faster on, where no feature tells
  them apart. Like `extra`, it is not trusted: it only
  says when the dispatcher may choose the implementation, and means nothing
  for a base, which the dispatcher falls back on. -/
  vendor : Option String := none
  /-- Microarchitectures (`verified_garbage_cpu::TUNING`), by their names,
  on which its function's dispatcher never chooses it, but tries the next
  implementation: the cores it is measured slower on than the one it falls
  through to. Not for a base, which the dispatcher falls back on. Like
  `extra`, it is not trusted: it only says when the dispatcher may choose the
  implementation, and keeping one from being chosen can only leave another
  the CPU can run, the base at last, which needs no feature. -/
  notWith : List String := []
  /-- A proof that the function returns without secret residue
  (`Target.noResidue`), or `none`. Every artifact of a target that defines
  it has one, but those `ci/residue_allowlist.txt` lists, as the emitter
  checks (`Rust.checkResidue`); none is possible on a target that does not. -/
  residue : Option (PLift (target.noResidue.elim False fun R =>
      R code contract (sig.retBits ((target.abi.withConsts consts).withTables sig tables).ptrBits)))
      := none

/-- Proves `Registration.spSafe`, by default. `Proof/Framework/Registration.lean`
implements it, with the proofs the kernel checks fastest on each ISA; how it
is proven is not trusted. -/
syntax (name := spSafe) "sp_safe" : tactic

/-- Proves `Registration.ofSig`, by default. `Proof/Framework/Registration.lean`
implements it; how it is proven is not trusted. -/
syntax (name := ofSig) "of_sig" : tactic

/-- Gives `Registration.consts`, by default: the tables of constants of the
calling convention `Abi.withConsts` makes in the contract `verified` proves
(`ConstsOf`). `Proof/Framework/Registration.lean` implements it; what it
gives is not trusted, since the contract must be `api`'s for those tables
(`Registration.ofApi`), and the emitter writes exactly those tables
(`Artifact.consts`). -/
syntax (name := constsOf) "consts_of" : tactic

/-- The tables of constants of a function whose contract is `contract`
(`Registration.consts`): a list of them, whose type names the contract so
that `consts_of` can find them in it. -/
abbrev ConstsOf {M : ISA} (_contract : Contract M) : Type := List (String × List (BitVec 64))

/-- Gives `Registration.stack`, by default: the `stack` of the `Sig.contract`
that the contract `verified` proves is (`StackOf`).
`Proof/Framework/Registration.lean` implements it; what it gives is not
trusted, since the contract must be `api`'s for that stack
(`Registration.ofApi`), and one that `Sig.contract` derives for it
(`Registration.ofSig`), whose requirements the emitter documents for exactly
that stack (`Artifact.stack`). -/
syntax (name := stackOf) "stack_of" : tactic

/-- The stack that the calls and frames of a function whose contract is
`contract` use, in bytes (`Registration.stack`): a number, whose type names
the contract so that `stack_of` can find it in it. -/
abbrev StackOf {M : ISA} (_contract : Contract M) : Type := Nat

/-- The value of `f` on the code of each call of `calls` (`Code.calls`), in
order, but for a call whose value is that of the first call of the same
function.

`calls` holds a function once per call of it, through every function that
calls it, and its code is usually the same value in memory at each of them:
`withPtrEq` finds that at once, without computing `f` again (which, on the
code of every call, was most of the time of the checks using this). -/
def Code.distinctCalls {I C β : Type} [BEq β] [LawfulBEq β] (f : Code I C → β)
    (calls : List (String × Code I C)) : List β := Id.run do
  -- The first call of each function so far, with its code and its value.
  let mut first : List {p : String × Code I C × β // p.2.2 = f p.2.1} := []
  let mut values : List β := []
  for (n, body) in calls do
    match first.find? (·.1.1 == n) with
    | some ⟨(_, body₀, v₀), h₀⟩ =>
      unless withPtrEq body body₀ (fun _ => f body == v₀) (fun h => by simp_all) do
        values := f body :: values
    | none =>
      let v := f body
      first := ⟨(n, body, v), rfl⟩ :: first
      values := v :: values
  return values.reverse

/-- The features that the instructions of `c` require, but not those of the
functions it calls, each once, in first-seen order after those of `acc`. -/
def Code.ownRequires {I C : Type} (req : I → List String) : List String → Code I C → List String
  | acc, .block is => is.foldl (fun acc i => add acc (req i)) acc
  | acc, .seq a b => ownRequires req (ownRequires req acc a) b
  | acc, .ite _ t e => ownRequires req (ownRequires req acc t) e
  | acc, .loop b _ => ownRequires req acc b
  | acc, .call _ _ => acc
  | acc, .frame i b j => add (ownRequires req (add acc (req i)) b) (req j)
  | acc, .icall i _ _ n => ownRequires req (add acc (req i)) n
where
  add (acc fs : List String) : List String :=
    fs.foldl (fun acc f => if acc.contains f then acc else acc ++ [f]) acc

/-- The calls in `c`, and in the functions it calls, as `Code.calls`, but
not those of an indirect call (`Code.icall`), nor any in the functions it
may reach: the calls whose code's features `Code.requires` counts. -/
def Code.reqCalls {I C : Type} : Code I C → List (String × Code I C)
  | .block _ => []
  | .seq a b => reqCalls a ++ reqCalls b
  | .ite _ t e => reqCalls t ++ reqCalls e
  | .loop b _ => reqCalls b
  | .call n b => (n, b) :: reqCalls b
  | .frame _ b _ => reqCalls b
  | .icall _ _ _ nx => reqCalls nx

/-- The features that the instructions of `c`, and of the functions it
calls, require (`Code.requires`), each once: those of the instructions of
`c` outside its calls (`ownRequires`), then those of the code of each call
(`reqCalls`, which has every call, those in the code of a call too, but not
the functions an indirect call may reach),
skipping a call whose code requires what the first call of the same
function's does (`distinctCalls`). These are the features of
`dedup (c.requires req)`, without building the list with repetitions or
going through the code of a function once per call of it. -/
def Code.requiresDedup {I C : Type} (req : I → List String) (c : Code I C) : List String :=
  (distinctCalls (ownRequires req []) (reqCalls c)).foldl ownRequires.add (ownRequires req [] c)

/-- `api`'s contract under the calling convention `A`, for an implementation
whose calls and frames use `stack` bytes of stack (`Api.contracts`), or, if
`api` has none, one that no state satisfies, which `Verified` rejects. -/
def Api.contract {M : ISA} (api : Api) (A : Abi M) (stack : Nat) : Contract M :=
  match api.contracts with
  | some f => f A stack
  | none => ⟨fun _ => False, fun _ _ => False, fun _ _ => False⟩

/-- An implementation of `api` on `target`: what a registration file states
of a function made from `api` (see `Api.artifact`). -/
structure Registration (api : Api) (target : Target) where
  /-- What follows `api`'s name in the function's: that of the CPU features
  or other variant it is for (e.g. `_avx2`), or nothing. -/
  suffix : String := ""
  /-- `Artifact.tables`. -/
  tables : List (String × List FnTable) := []
  code : Prog target.isa
  /-- The contract `verified` proves, which is `api`'s on `target` for
  `consts`, `tables` and `stack` (`ofApi`); unification finds it in
  `verified`'s type. The default, for a `verified` whose type does not
  determine it, is `api`'s for no tables of constants and no stack. -/
  contract : Contract target.isa :=
    api.contract (target.abi.withTables api.sig tables) 0
  verified : Verified target code contract
  /-- `Artifact.consts`: by default, those `contract` names (`consts_of`),
  so that a registration states them only where it does not. -/
  consts : ConstsOf contract := by consts_of
  /-- `Artifact.stack`: by default, that of `contract` (`stack_of`), so that
  a registration never states it. -/
  stack : StackOf contract := by stack_of
  ofApi : contract = api.contract ((target.abi.withConsts consts).withTables api.sig tables) stack := by
    exact rfl
  /-- `Artifact.ofSig`. -/
  ofSig : ∃ pre post leak,
      contract = api.sig.contract
        (((target.abi.withConsts consts).withTables api.sig tables).withMode api.pubMode) pre post
        api.writeArgs stack leak := by
    of_sig
  /-- `Artifact.spSafe`. -/
  spSafe : code.all (fun i => !target.isa.writesSp i) = true := by sp_safe
  /-- `Artifact.written`. -/
  written : List (String × Nat) := []
  /-- `Artifact.writtenOk`. -/
  writtenOk : ∀ s t s', contract.pre s → Exec target.isa code s t s' →
      Sig.writtenWithin target.abi api.sig written s s' := by
    exact fun _ _ _ _ _ => True.intro
  /-- `Artifact.extra`. -/
  extra : List String := []
  /-- `Artifact.vendor`. -/
  vendor : Option String := none
  /-- `Artifact.notWith`. -/
  notWith : List String := []
  /-- `Artifact.residue`. -/
  residue : Option (PLift (target.noResidue.elim False fun R =>
      R code contract (api.sig.retBits ((target.abi.withConsts consts).withTables api.sig tables).ptrBits)))
      := none

/-- The artifact of the implementation `r` of `api` on `target`: its module,
signature and `writeArgs` are `api`'s, its name `api`'s followed by
`r.suffix` (its `base` `api`'s), its documentation `api`'s (`Api.doc`), and its
contract `api`'s on `target`, for `r.consts`, `r.tables` and `r.stack`
(`Api.contract`), which makes the mode public if `api.pubMode`; its CPU
features those its code requires (`Code.requiresDedup`); its code is
printed and documented with `target`'s ISA's `Emitter` (`EmitTarget.of`). -/
def Api.artifact (api : Api) (target : Target) [Emitter target.isa] (r : Registration api target) :
    Artifact where
  target := .of target
  module := api.module
  name := api.name ++ r.suffix
  base := api.name
  sig := api.sig
  doc := api.doc
  consts := r.consts
  tables := r.tables
  code := r.code
  contract := r.contract
  verified := r.verified
  writeArgs := api.writeArgs
  stack := r.stack
  pubMode := api.pubMode
  ofSig := r.ofSig
  contracts := api.contracts
  ofApi := by
    rw [r.ofApi]
    unfold Api.contract
    cases api.contracts <;> exact (by trivial)
  spSafe := r.spSafe
  features := Code.requiresDedup target.isa.requires r.code
  written := r.written
  writtenOk := r.writtenOk
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  residue := r.residue

end VG
