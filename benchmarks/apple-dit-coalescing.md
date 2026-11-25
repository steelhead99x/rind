# Coalescing DIT toggles beyond one call: design and prototype

For fork issues #259 to #266. Status: a measuring prototype behind
`--cfg rind_dit_autohold`, off by default, refused by the FIPS module. No
speed is claimed: nothing here has run on Apple hardware.

## Where coalescing stands

- Within one call: one toggle (PR #299, counted by
  `low::entry::tests::each_call_costs_its_toggles` for 75 calls).
- Across calls, by the caller: `cpu::Dit::hold`, `with`, `batch` (PRs #293,
  #299). Exact, and the caller decides which of its own code runs with DIT.
- Across calls, by rind alone: `--cfg rind_dit_sticky` (PR #291) never
  clears DIT once set. It measures the whole toggle cost, but leaves every
  later instruction on the thread under DIT, forever.

The gap: an application (or an adapter such as rind-rustls, whose upstream
API has no batch hook) that makes many small secret calls in a row and will
not, or cannot, take a guard.

## The prototype: a bounded thread-local batch

`rind/src/low/entry.rs`, `mod autohold`:

1. When the last secret `Entry` on a thread drops and rind had set DIT for
   it, DIT stays on, and the thread enters a batch.
2. Later secret calls find DIT on and toggle nothing; each counts against
   the batch.
3. The batch ends, and rind clears DIT, at the first of:
   - a public call into rind made outside any secret `Entry` or guard (a
     signature verification, parsing a public key): the thread has moved
     on to public work;
   - the 65th secret call in a row (`autohold::BATCH = 64`), so a thread
     that keeps calling rind, but never with a public call, still has DIT
     cleared every 65 secret calls.

   Both bounds count calls into rind, not time: a thread whose last call
   into rind is a secret one keeps DIT on for all its own code until it
   calls rind again or exits (see "No end without rind" under Risks).
4. A guard's drop still clears DIT at once, as `cpu::Dit`'s docs promise,
   and a batch never clears DIT while a guard is held.
5. DIT rind did not set (the caller's own `msr DIT, #1`) is never cleared:
   a call that found DIT on starts no batch.

Tests: `autohold_batches_until_a_public_call_or_its_limit`, and the whole
`low::entry` and `low::aarch64::cpu` suites pass under qemu-aarch64 with
`--cfg rind_dit_everywhere --cfg rind_dit_autohold`. `admin/dit-qemu` passes
too: every instruction of every call after DIT is set runs with it set.

## Threat reasoning

What DIT protects, and when it must be on:

- Arm's definition (ARM ARM B1.5.6) covers the instructions from the
  change of PSTATE.DIT to 1 to the change back to 0, speculative ones
  included, and the values they read, hardware prefetches included. A value
  read outside that window, even speculatively, is not covered. So DIT must
  be on before a secret is loaded and stay on until the last instruction
  that touches it; it does not have to be on at any other time.
- GoFetch (Chen et al., USENIX Security 2024) drives Apple's data
  memory-dependent prefetcher (DMP) with secret-dependent values the victim
  loads; on M3, setting DIT disables the DMP (the paper's footnote 22; not
  so on M1 and M2). The attack needs the DMP active while secret-derived
  values pass through loads, which is rind's computation.

So the security property is "DIT on whenever rind's code handles a
secret", and coalescing is safe exactly when it only ever delays clearing
DIT. The prototype never clears DIT inside a secret `Entry` (it counts live
entries), never starts a secret computation without DIT (every secret
`Entry` still sets DIT if it finds it clear), and only clears in the two
places above. Holding DIT longer cannot weaken the guarantee for rind's
secrets.

## Risks

- **The caller's own code runs with DIT** between calls in a batch: up to
  64 calls' worth of the application's code. For the application's own
  secrets that is harmless or helpful. For its performance it is unknown:
  DIT turns off the DMP on M3 and later, which may slow pointer-chasing
  code (the DMP exists to speed it up), and DIT may change other timings on
  Apple cores. This is the measurement that decides the idea.
- **Surprise.** A library leaving a CPU mode on after it returns is
  unusual. rind documents that guards hold DIT; it would also have to
  document that calls may leave it on. A caller that reads PSTATE.DIT, or
  that sets and clears DIT itself, could be confused: a caller that sets
  DIT during a batch (a no-op, since it is on) loses it when the batch
  ends.
- **The bound is a heuristic.** 64 calls is arbitrary. A time bound would
  need a clock read per call, which costs more than the toggle it saves.
- **No end without rind.** A thread that makes one secret call and then
  runs its own code for an hour keeps DIT on for that hour, unless it calls
  rind again. Only the guard API gives the caller that control.
- **Threads.** The batch is thread-local, like DIT. A thread that ends in a
  batch dies with DIT on, which costs nothing. Linux copies PSTATE to a new
  thread, so a thread spawned during a batch starts with DIT on and no
  batch of its own, so rind never clears it there: it only adds DIT.

## How to measure it

The DIT bench matrix (fork issues #259 to #266) gains one build:

    RUSTFLAGS='--cfg rind_dit_autohold' cargo bench -p rind-bench $B

against the default, sticky, and held rows. If autohold matches sticky on
the per-call rows (QUIC header protection, tiny AEAD, HMAC at 1350 B) and
the caller-side cost of DIT is within noise on a pointer-heavy workload, it
is worth proposing; otherwise the guard API stays the only coalescing
across calls.

## Decision (project owner, 2026-11-23)

Autohold stays a measuring prototype only. The supported way to coalesce
toggles across calls is the guard API: `Dit::hold`, `Dit::with`, and
`Dit::batch` (benchmarks/apple-dit-barrier.md, "Decision").

## Recommendation

Keep the guard API (`Dit::hold`, `with`, `batch`) as the supported answer,
and adapters' batch hooks where their upstreams have them. Treat autohold as
a measurement, and a decision for the owner after M1 and iPad numbers: it
changes what callers' code runs under, which only the owner can accept.
