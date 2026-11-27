# DIT coverage on Apple aarch64: audit and checks

For fork issues #259 to #266. This is what was checked, by construction and
by test, about which of rind's instructions run with PSTATE.DIT set on
Apple's aarch64 targets (and on any aarch64 OS under `--cfg
rind_dit_everywhere`), what was wrong, and what remains. No Apple hardware
was used: the dynamic checks ran under qemu-aarch64's `max` CPU, which has
FEAT_DIT.

## The discipline

- A public function that handles a secret makes a secret `Entry`
  (`rind/src/low/entry.rs`) before touching it. Making the first one on a
  thread sets DIT if it is clear (`dit::maybe_enable` reads PSTATE.DIT
  first); dropping it clears DIT only if that `Entry` set it. So rind never
  clears DIT a caller set, and nested entries toggle nothing.
- A public function on public data makes a public `Entry`, which sets no DIT.
- `crate::cpu::Dit` guards hold DIT across calls; the last one to drop
  restores what the first one found.
- In a debug build where rind sets DIT, every secret `Entry`, its drop, and
  every primitive's `Entry::assert_held` read PSTATE.DIT and panic if it is
  clear while a secret `Entry` is live.

## The two automated checks

**Static: `admin/dit-coverage`** (run by `sh/dispatch.sh`'s `dit` module, so
by every gate run that touches `rind/src/`). It scans every `pub fn` of the
public API (all of `rind/src/` outside `low/` and tests: 287 today) and
fails unless each one makes an `Entry` (70 secret, 17 public) or is listed
in `admin/dit-coverage.txt` as `accessor`, `delegates` (named callee makes
its own `Entry`), or `public`, with a reason. It also fails on a stale
listing, on a listed function that now makes an `Entry`, and on a public
`Entry` in a function whose name says it handles a secret (`sign`, `agree`,
`to_scalar`, ...). A new public function cannot ship unclassified.

What it does not do: follow calls. A `delegates` entry is a reviewed claim,
and the dynamic check is what proves the callee sets DIT.

**Dynamic: `admin/dit-qemu`** with `admin/dit-qemu-plugin.c` (CI:
`ctgrind.yml`'s `dit-qemu` job, on pull requests too; locally
`nix develop .#dit-qemu --command admin/dit-qemu`). The test
`low::entry::tests::dit_qemu_every_secret_call` runs each of the 75 calls in
`low::entry::tests::calls` between two `hint` marks; the plugin reads
PSTATE.DIT (bit 24 of qemu's `cpsr`) at every instruction executed between
them, in every function: rind's Rust, its imported assembly (s2n-bignum,
aws-lc, verified-garbage), core, and libc's `memcpy`. It fails a call that:

- never set DIT;
- ran any instruction with DIT clear between two that ran with it set (a
  second toggle inside one call, or something clearing DIT under a live
  `Entry`): a hole;
- ran code in `rind::low::` or `rind::mid::` before first setting DIT, other
  than the `Entry` and feature detection that set it, unless the call lists
  it with a reason (parsing the peer's public key in an agreement).

Two planted windows (a hole, and no DIT at all) must each be caught, so a
plugin that reads nothing fails. Each call's setup runs between two more
marks that leave it out.

Result on the audit branch: all 75 calls set DIT, none has a hole, and
nothing secret runs before DIT is set.

## Gaps found and fixed (audit branch)

| Where | What | Fix |
|---|---|---|
| `rind/src/mid/mlkem.rs` `DecapKey::from_bytes` | decoded the secret polynomials of an expanded ML-KEM key under a **public** `Entry` (FIPS ACVP builds and tests) | secret `Entry` |
| `rind/src/fips/acvp.rs` `ml_kem_check_decapsulation_key` | copied a whole decapsulation key under a public `Entry` | secret `Entry` |
| `rind/src/fips/acvp.rs` `ml_kem_decap` | reached the decoder above before decapsulating | covered by the first fix |
| `rind/src/high/agreement.rs` `PrivateKey::to_scalar` | converted the private scalar's limbs to bytes with **no** `Entry` (X25519 and the NIST curves; `ecdsa::KeyPair::to_scalar` already had one) | secret `Entry` |
| `rind/src/high/oprf.rs` and `oprf/voprf.rs` `ServerKey::to_scalar` | same, for the OPRF key | secret `Entry` |
| `rind/src/high/vrf.rs` `KeyPair::to_seed` | same, for the P-256 VRF scalar | secret `Entry` |
| `rind/src/high/spake2plus.rs` `VerifierRecord::l` | encoded L, which its own docs say to keep like `w0`, under a public `Entry` | secret `Entry` (its arithmetic stays timed as public) |
| `rind/src/low/entry.rs` `Entry` | was `Send` and `Sync`; nothing moved one, but dropping it on another thread would corrupt both threads' DIT state | now neither, like `cpu::Dit` |

Each fixed export is now one of the 75 dynamic calls, and the toggle model
(`each_call_costs_its_toggles`) counts one toggle for each where it counted
none before.

## Checked and found sound

- **Caller-set DIT survives.** `a_caller_set_dit_survives_every_call_and_guard`:
  with DIT set before rind runs, all 75 calls, a guard, `with`, `batch`,
  guards dropped out of order, and a panic unwinding through `with` leave it
  set. `dit_returns_to_what_the_first_guard_found` pins the documented
  converse: a caller that sets DIT inside a guard rind took loses it at the
  last drop, so set it before.
- **Threads.** DIT is PSTATE, saved in SPSR on every exception, so it follows
  a thread across preemption and migration (Arm ARM B1.5.6). `Entry` and
  `Dit` are `!Send`, so neither can be dropped on another thread or held
  across an `.await` a work-stealing runtime may move. Linux copies PSTATE
  into a new thread, so a thread spawned under a guard can start with DIT
  set but holds no guard (`a_thread_spawned_under_a_guard_holds_nothing`);
  rind leaves such inherited DIT alone.
- **Signals.** `a_signal_handler_leaves_the_interrupted_dit`: a handler that
  makes a secret call leaves DIT as the handler found it, and a handler that
  returns with DIT set does not leak it into the interrupted code, because
  sigreturn restores PSTATE (Linux: `setup_return` leaves DIT alone,
  sigreturn restores it). Under qemu this checks qemu's emulation of Linux;
  XNU's behaviour (handler inherits DIT, per source reading) needs an Apple
  run.
- **Panics and early returns.** `Entry` is a drop guard, so `?`, early
  returns, and unwinding all run its drop. `a_panic_inside_a_guard_releases_it`
  covers guards. With `panic = "abort"` nothing runs after the panic.
- **Callbacks into user code.** rind's public traits are sealed and no public
  function takes a closure, so no user code runs under a secret `Entry`
  except the global allocator and a panic hook, which then run with DIT
  set (it only adds DIT).
- **fork.** The child inherits the forking thread's PSTATE and its
  thread-locals, so its DIT state and guard count stay consistent.

## Decisions for the owner

- **Wipes on drop run outside DIT.** Decided by the owner on 2026-11-23:
  they stay as they are, without DIT (benchmarks/apple-dit-barrier.md,
  "Decision"). The reasoning that decision rests on: A key type's `Drop` zeroises without an
  `Entry`. A wipe stores zeros: it loads none of the secret and computes on
  none of it, so no instruction's timing depends on the secret, and Apple's
  data memory-dependent prefetcher, which GoFetch drives through loaded
  values, is given none to load. Running each drop under a secret `Entry`
  would cost one toggle per dropped key outside a guard. Whether stores'
  read-for-ownership fills can feed the prefetcher on M3 and later is not
  documented anywhere found; if the owner wants the conservative choice, it
  is one `Entry` in `low::zeroise` and `zeroise_value`, and the toggle model
  will show what it costs. `admin/dit-qemu` allows `rind::low::generic::zeroise`
  before DIT for this reason.
- **Copies of key bytes outside an `Entry`** (`ChaCha20::new`, accessors such
  as `to_seed` for Ed25519 and ML-DSA, `SigningShare::to_scalar`) move the
  caller's own bytes and compute nothing; they stay outside, as `Entry`'s
  docs allow for accessors. The `ct::into_secret` markers they call are
  identity functions.
- **Secret values returned to the caller** are moved by the caller's code
  after the `Entry` drops. That is the caller's data from then on; a caller
  that wants it under DIT holds a guard.

## What remains for device runs

- Run the matrix checkout's correctness list (plan step 1) on the M1 and an
  iPad, which reads real PSTATE.DIT on Apple cores in every check above.
- `a_signal_handler_leaves_the_interrupted_dit` on macOS, to confirm XNU
  restores DIT on sigreturn.
