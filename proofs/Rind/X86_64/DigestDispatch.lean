import Rind.X86_64.Funs
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# The digest API's dispatch, modelled by hand

`Context` and `digest` reach each hash's code through function pointers, which
Aeneas cannot translate, so the translation starts below them and this file
models the Rust above them. `admin/prove` fails unless this quote is still
that Rust, so a change to it is a change to this model:

```rust
pub fn digest(algorithm: &'static Algorithm, data: &[u8]) -> Digest {
    let _entry = Entry::new_secret();
    (algorithm.hash)(data)
}

impl Context {
    /// Starts hashing with `algorithm`.
    // Inlined, so a context built in place, as by `Box::new`, writes just
    // its algorithm and tag there.
    #[inline]
    pub fn new(algorithm: &'static Algorithm) -> Self {
        Self(Computation {
            algorithm,
            state: State::Fresh,
        })
    }

    /// Adds `data` to the message.
    pub fn update(&mut self, data: &[u8]) {
        // The compressors enter instead, so an update that only buffers skips
        // the cost of enabling DIT.
        self.0.state.update(self.0.algorithm, data);
    }

    /// Returns the digest of the message, and starts a new one with the same algorithm.
    pub fn finish(&mut self) -> Digest {
        let _entry = Entry::new_secret();
        let digest = self.0.state.finish(self.0.algorithm);
        self.0.state = State::Fresh;
        digest
    }
}

impl State {
    fn update(&mut self, algorithm: &Algorithm, data: &[u8]) {
        match self {
            Self::Fresh => (algorithm.start)(self, data),
            Self::Md5(hashing) => hashing.update(data),
            Self::Sha1(hashing) => hashing.update(data),
            Self::Sha256(hashing) => hashing.update(data),
            Self::Sha384(hashing) => hashing.update(data),
            Self::Sha512(hashing) => hashing.update(data),
            Self::Sha512_256(hashing) => hashing.update(data),
            Self::Sha3_256(hashing) => hashing.update(data),
            Self::Sha3_384(hashing) => hashing.update(data),
            Self::Sha3_512(hashing) => hashing.update(data),
        }
    }

    fn finish(&self, algorithm: &Algorithm) -> Digest {
        match self {
            Self::Fresh => (algorithm.hash)(&[]),
            Self::Md5(hashing) => hashing.finish(),
            Self::Sha1(hashing) => hashing.finish(),
            Self::Sha256(hashing) => hashing.finish(),
            Self::Sha384(hashing) => hashing.finish(),
            Self::Sha512(hashing) => hashing.finish(),
            Self::Sha512_256(hashing) => hashing.finish(),
            Self::Sha3_256(hashing) => hashing.finish(),
            Self::Sha3_384(hashing) => hashing.finish(),
            Self::Sha3_512(hashing) => hashing.finish(),
        }
    }
}

struct Hashing<C: Variant> {
    ops: &'static Ops<C>,
    context: C,
}

struct Ops<C> {
    update: fn(&mut C, &[u8]),
    finish: fn(&C) -> Digest,
}

impl<C: Variant> Hashing<C> {
    /// Starts `state` hashing with `C`, from `data`, building the context
    /// where `state` lives.
    fn start(state: &mut State, data: &[u8]) {
        *state = C::state(Self {
            ops: const {
                &Ops {
                    update: C::update,
                    finish: C::finish,
                }
            },
            context: C::NEW,
        });
        if let Some(hashing) = C::hashing(state) {
            hashing.context.update(data);
        }
    }

    fn update(&mut self, data: &[u8]) {
        (self.ops.update)(&mut self.context, data)
    }

    fn finish(&self) -> Digest {
        (self.ops.finish)(&self.context)
    }
}

fn one_shot<C: Variant>(data: &[u8]) -> Digest {
    let mut context = C::NEW;
    context.update(data);
    context.finish()
}

trait Variant: HashContext + Copy + 'static {
    /// A context before any input.
    // A constant rather than a function, so starting a context copies it
    // from read-only memory instead of building it on the stack.
    const NEW: Self;

    fn state(hashing: Hashing<Self>) -> State;

    /// The `Hashing` `state` holds, if it is this hash's.
    fn hashing(state: &mut State) -> Option<&mut Hashing<Self>>;
}

```

The model departs from the Rust in two ways, and adds no axiom:

- `Ops<C>` holds nothing, and `Hashing`'s methods call `C`'s `HashContext`
  `update` and `finish` directly: `Ops` is private to
  `high::digest`, whose only value of one is `Hashing::start`'s, of those two.
  `admin/prove` checks that the quote holds every mention of `Ops` there.
- `Algorithm`'s `hash` and `start` are functions of which static it is,
  as `Rind.X86_64.DigestAlgorithm` models `Algorithm`, each the function that
  static holds there.
-/

namespace rind.x86_64

/-- `Hashing::<C>::start`, which overwrites `state`, then updates it in place. -/
def high.digest.Hashing.start {C : Type} (VariantInst : high.digest.Variant C)
    (_state : high.digest.State) (data : Slice Std.U8) : Result high.digest.State := do
  let context ← VariantInst.NEW
  let state ← VariantInst.state { context, ops := () }
  let (hashing, back) ← VariantInst.hashing state
  match hashing with
  | none => ok (back none)
  | some hashing => do
    let context ← VariantInst.hashHashContextInst.update hashing.context data
    ok (back (some { hashing with context }))

/-- `Hashing::<C>::update`, whose `ops.update` is `C::update`. -/
def high.digest.Hashing.update {C : Type} (VariantInst : high.digest.Variant C)
    (self : high.digest.Hashing C) (data : Slice Std.U8) : Result (high.digest.Hashing C) := do
  let context ← VariantInst.hashHashContextInst.update self.context data
  ok { self with context }

/-- `Hashing::<C>::finish`, whose `ops.finish` is `C::finish`. -/
def high.digest.Hashing.finish {C : Type} (VariantInst : high.digest.Variant C)
    (self : high.digest.Hashing C) : Result high.digest.Digest :=
  VariantInst.hashHashContextInst.finish self.context

/-- `one_shot::<C>`. -/
def high.digest.one_shot {C : Type} (VariantInst : high.digest.Variant C) (data : Slice Std.U8) :
    Result high.digest.Digest := do
  let context ← VariantInst.NEW
  let context ← VariantInst.hashHashContextInst.update context data
  VariantInst.hashHashContextInst.finish context

/-- The function each static holds as `hash`. -/
def high.digest.Algorithm.hash (algorithm : high.digest.Algorithm) (data : Slice Std.U8) :
    Result high.digest.Digest :=
  match algorithm with
  | .MD5 => do
      let initial ← mid.md5.Md5State.new
      let output ← mid.md5.Md5State.finish_with initial data
      let algorithm ← high.digest.MD5
      high.digest.Digest.new algorithm (Array.to_slice output)
  | .SHA1 => high.hash.Hash.hash.default
      high.hash.LegacySha1.Insts.RindHighHashHashSha1ContextSha1State data
  | .SHA256 => high.hash.Hash.hash.default
      high.hash.Sha256.Insts.RindHighHashHashSha256ContextSha256State data
  | .SHA384 => high.hash.Hash.hash.default
      high.hash.Sha384.Insts.RindHighHashHashSha384ContextSha384State data
  | .SHA512 => high.hash.Hash.hash.default
      high.hash.Sha512.Insts.RindHighHashHashSha512ContextSha512State data
  | .SHA512_256 => do
      let initial ← mid.sha2.Sha512_256Context.INITIAL
      let output ← mid.sha2.Sha512State.finish_with initial data
      let algorithm ← high.digest.SHA512_256
      let truncated ← mid.sha2.Sha512_256Context.truncate output
      high.digest.Digest.new algorithm (Array.to_slice truncated)
  | .SHA3_256 => high.digest.one_shot high.digest.Sha3_256Context.Insts.RindHighDigestVariant data
  | .SHA3_384 => high.digest.one_shot high.digest.Sha3_384Context.Insts.RindHighDigestVariant data
  | .SHA3_512 => high.digest.one_shot high.digest.Sha3_512Context.Insts.RindHighDigestVariant data

/-- The function each static holds as `start`. -/
def high.digest.Algorithm.start :
    high.digest.Algorithm → high.digest.State → Slice Std.U8 → Result high.digest.State
  | .MD5 => high.digest.Hashing.start high.digest.Md5Context.Insts.RindHighDigestVariant
  | .SHA1 => high.digest.Hashing.start high.hash.Sha1Context.Insts.RindHighDigestVariant
  | .SHA256 => high.digest.Hashing.start high.hash.Sha256Context.Insts.RindHighDigestVariant
  | .SHA384 => high.digest.Hashing.start high.hash.Sha384Context.Insts.RindHighDigestVariant
  | .SHA512 => high.digest.Hashing.start high.hash.Sha512Context.Insts.RindHighDigestVariant
  | .SHA512_256 =>
    high.digest.Hashing.start high.digest.Sha512_256Context.Insts.RindHighDigestVariant
  | .SHA3_256 => high.digest.Hashing.start high.digest.Sha3_256Context.Insts.RindHighDigestVariant
  | .SHA3_384 => high.digest.Hashing.start high.digest.Sha3_384Context.Insts.RindHighDigestVariant
  | .SHA3_512 => high.digest.Hashing.start high.digest.Sha3_512Context.Insts.RindHighDigestVariant

/-- `digest`. -/
def high.digest.digest (algorithm : high.digest.Algorithm) (data : Slice Std.U8) :
    Result high.digest.Digest := do
  let _ ← low.entry.Entry.new_secret
  algorithm.hash data

/-- `State::update`. -/
def high.digest.State.update (self : high.digest.State) (algorithm : high.digest.Algorithm)
    (data : Slice Std.U8) : Result high.digest.State :=
  match self with
  | .Fresh => algorithm.start self data
  | .Md5 hashing => do
    let hashing ← high.digest.Hashing.update high.digest.Md5Context.Insts.RindHighDigestVariant hashing data
    ok (.Md5 hashing)
  | .Sha1 hashing => do
    let hashing ← high.digest.Hashing.update high.hash.Sha1Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha1 hashing)
  | .Sha256 hashing => do
    let hashing ← high.digest.Hashing.update high.hash.Sha256Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha256 hashing)
  | .Sha384 hashing => do
    let hashing ← high.digest.Hashing.update high.hash.Sha384Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha384 hashing)
  | .Sha512 hashing => do
    let hashing ← high.digest.Hashing.update high.hash.Sha512Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha512 hashing)
  | .Sha512_256 hashing => do
    let hashing ← high.digest.Hashing.update
      high.digest.Sha512_256Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha512_256 hashing)
  | .Sha3_256 hashing => do
    let hashing ← high.digest.Hashing.update
      high.digest.Sha3_256Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha3_256 hashing)
  | .Sha3_384 hashing => do
    let hashing ← high.digest.Hashing.update
      high.digest.Sha3_384Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha3_384 hashing)
  | .Sha3_512 hashing => do
    let hashing ← high.digest.Hashing.update
      high.digest.Sha3_512Context.Insts.RindHighDigestVariant hashing data
    ok (.Sha3_512 hashing)

/-- `State::finish`. -/
def high.digest.State.finish (self : high.digest.State) (algorithm : high.digest.Algorithm) :
    Result high.digest.Digest :=
  match self with
  | .Fresh => algorithm.hash (Array.to_slice (Std.Array.empty Std.U8))
  | .Md5 hashing =>
    high.digest.Hashing.finish high.digest.Md5Context.Insts.RindHighDigestVariant hashing
  | .Sha1 hashing =>
    high.digest.Hashing.finish high.hash.Sha1Context.Insts.RindHighDigestVariant hashing
  | .Sha256 hashing =>
    high.digest.Hashing.finish high.hash.Sha256Context.Insts.RindHighDigestVariant hashing
  | .Sha384 hashing =>
    high.digest.Hashing.finish high.hash.Sha384Context.Insts.RindHighDigestVariant hashing
  | .Sha512 hashing =>
    high.digest.Hashing.finish high.hash.Sha512Context.Insts.RindHighDigestVariant hashing
  | .Sha512_256 hashing =>
    high.digest.Hashing.finish high.digest.Sha512_256Context.Insts.RindHighDigestVariant hashing
  | .Sha3_256 hashing =>
    high.digest.Hashing.finish high.digest.Sha3_256Context.Insts.RindHighDigestVariant hashing
  | .Sha3_384 hashing =>
    high.digest.Hashing.finish high.digest.Sha3_384Context.Insts.RindHighDigestVariant hashing
  | .Sha3_512 hashing =>
    high.digest.Hashing.finish high.digest.Sha3_512Context.Insts.RindHighDigestVariant hashing

/-- `Context::new`. -/
def high.digest.Context.new (algorithm : high.digest.Algorithm) : Result high.digest.Context :=
  ok { algorithm, state := .Fresh }

/-- `Context::update`. -/
def high.digest.Context.update (self : high.digest.Context) (data : Slice Std.U8) :
    Result high.digest.Context := do
  let state ← high.digest.State.update self.state self.algorithm data
  ok { self with state }

/-- `Context::finish`. -/
def high.digest.Context.finish (self : high.digest.Context) :
    Result (high.digest.Digest × high.digest.Context) := do
  let _ ← low.entry.Entry.new_secret
  let digest ← high.digest.State.finish self.state self.algorithm
  ok (digest, { self with state := .Fresh })

/-- The empty message `State::finish` hashes for a fresh context. -/
@[simp] theorem high.digest.empty_slice_val :
    (Array.to_slice (Std.Array.empty Std.U8)).val = [] := rfl

@[simp] theorem high.digest.empty_array_val : (Std.Array.empty Std.U8).val = [] := rfl

/-- A context finished before any update returns `digest` of the empty
message, and stays fresh. -/
theorem high.digest.Context.finish_fresh (a : high.digest.Algorithm)
    {P : high.digest.Digest × high.digest.Context → Prop}
    (h : high.digest.digest a (Array.to_slice (Std.Array.empty Std.U8)) ⦃ d =>
      P (d, { algorithm := a, state := .Fresh }) ⦄) :
    high.digest.Context.finish { algorithm := a, state := .Fresh } ⦃ P ⦄ := by
  unfold high.digest.digest at h
  have heq : high.digest.Context.finish { algorithm := a, state := .Fresh } =
      Std.bind (do
        let _ ← low.entry.Entry.new_secret
        a.hash (Array.to_slice (Std.Array.empty Std.U8)))
        (fun d => ok (d, { algorithm := a, state := .Fresh })) := by
    simp [high.digest.Context.finish, high.digest.State.finish]
  rw [heq]
  exact WP.spec_bind h fun d hd => by simpa using hd

end rind.x86_64
