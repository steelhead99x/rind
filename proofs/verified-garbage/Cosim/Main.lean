import Cosim.X86_64
import Cosim.AArch64
import Cosim.Rind
import Std.Data.HashMap

/-!
# `vg-cosim`

`vg-cosim <arch> <groups | --rind> <cases> <seed> <cpu-features> <cpu-out> [<emulator-features> <emulator-out>]`
reads the groups of lines of VG's code that `admin/vg-bytes` wrote, each
its kind, its text and its machine code, and writes to `cpu-out` the stream
`admin/vg-cosim-runner.rs` reads: `cases` random cases of each instruction
whose CPU features are all among `cpu-features` (comma-separated Rust
`target_feature` names, which the runner's `--features` prints). With
`emulator-features`, the features of the emulator the runner also runs
under, it writes each other instruction to `emulator-out`, and fails if the
emulator lacks a feature it needs too, since then nothing would check it.
It fails if a group is not an instruction of the model, or the model faults
in every state tried. With `--rind` for `groups`, on aarch64, it writes the
cases of the functions rind proves in its own model instead
(`Cosim/Rind.lean`).
-/

open Cosim

def main (args : List String) : IO UInt32 := do
  let (arch, groups, n, seed, feats, cpuOut, emu) ← match args with
    | [a, g, n, s, f, o] => pure (a, g, n, s, f, o, none)
    | [a, g, n, s, f, o, e, eo] => pure (a, g, n, s, f, o, some (e, eo))
    | _ =>
      IO.eprintln "usage: vg-cosim <x86_64|aarch64> <groups | --rind> <cases> <seed> <cpu-features> <cpu-out> \
        [<emulator-features> <emulator-out>]"
      return 2
  let some n := n.toNat? | IO.eprintln "vg-cosim: cases is not a number"; return 2
  if n == 0 then IO.eprintln "vg-cosim: cases must be at least 1"; return 2
  let some seed := seed.toNat? | IO.eprintln "vg-cosim: seed is not a number"; return 2
  unless arch == "x86_64" || arch == "aarch64" do
    IO.eprintln s!"vg-cosim: no model of {arch}"; return 2
  let split (s : String) := (s.splitOn ",").filter (· != "")
  let host := split feats
  let emulator := emu.map (split ·.1)
  let (archByte, stateLen) := match arch with
    | "x86_64" => ((0 : UInt8), X86_64.stateLen)
    | _ => (1, AArch64.stateLen)
  let cpu ← IO.FS.Handle.mk cpuOut .write
  let emuH ← emu.mapM (IO.FS.Handle.mk ·.2 .write)
  cpu.write (header archByte stateLen)
  if let some h := emuH then h.write (header archByte stateLen)
  let mut errors : Array String := #[]
  let mut counts := (0, 0, 0, 0)
  let mut missing : Std.HashMap String Nat := {}
  let mut rng : UInt64 := seed.toUInt64
  let gens ← if groups == "--rind" then
      if arch != "aarch64" then
        IO.eprintln "vg-cosim: rind's model is of aarch64 only"; return 2
      pure [Rind.blocks n]
    else
      (← IO.FS.lines groups).toList.mapM fun line => do
        let [kind, text, hex] := line.splitOn "\t" | return pure (.error s!"bad line: {line}")
        let some code := parseHex hex | return pure (.error s!"bad bytes: {line}")
        let lines := text.splitOn "; "
        return match arch with
          | "x86_64" => X86_64.blocks kind lines code n
          | _ => AArch64.blocks kind lines code n
  for gen in gens do
    let (res, rng') := gen.run rng
    rng := rng'
    match res with
    | .error e => errors := errors.push e
    | .ok bs =>
      for (b, req) in bs do
        let lacks := req.filter (!host.contains ·)
        if lacks.isEmpty then
          cpu.write b.encode
          counts := (counts.1 + 1, counts.2.1 + b.cases.size, counts.2.2)
          continue
        for f in lacks do
          missing := missing.insert f (missing.getD f 0 + 1)
        let (some e, some h) := (emulator, emuH) | continue
        let absent := req.filter (!e.contains ·)
        if !absent.isEmpty then
          errors := errors.push s!"{b.text} needs {", ".intercalate absent}, \
            which this CPU lacks some of and the emulator lacks"
          continue
        h.write b.encode
        counts := (counts.1, counts.2.1, counts.2.2.1 + 1, counts.2.2.2 + b.cases.size)
  cpu.write trailer
  if let some h := emuH then h.write trailer
  let lacking := ", ".intercalate (missing.toList.map fun (f, k) => s!"{f} ({k})")
  let (c, cc, e, ec) := counts
  IO.eprintln s!"vg-cosim: {arch}: {c} instructions, {cc} cases for this CPU; \
    {e} instructions, {ec} cases for the emulator\
    {if lacking.isEmpty then "" else s!"; this CPU lacks {lacking}"}"
  for e in errors do
    IO.eprintln s!"vg-cosim: {e}"
  return if errors.isEmpty then 0 else 1
