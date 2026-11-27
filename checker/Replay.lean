import Lean.CoreM
import Lean.Replay
open Lean

/-!
# lemmata-replay

Kernel re-check of an exact list of modules: every constant the listed modules define goes
through Lean's kernel again, read from their compiled files.

    lemmata-replay <file with one module name per line>
    lemmata-replay --per-module <file with one module name per line>
    lemmata-replay --imports <file with one module name per line>     (checks nothing)

Exits 0 only if every constant of every listed module is accepted. A listed module without an
olean is an error. (`leanchecker <names>` selects every module that has a name as a *prefix*, so
`leanchecker Lemmata` replays the whole archive, and it exits 0 when no olean matches a name.)

## One pass (the default, since 2026-11-22)

The imports of the listed modules that are not listed themselves (Mathlib, Lean core, ...) are
loaded once and trusted, as `leanchecker` trusts the imports of every module it checks. Then every
constant of every listed module goes through the kernel once, in dependency order, by
`Kernel.Environment.replay` from `Lean.Replay`, the function `leanchecker` uses: each one checked
against the trusted imports and the archive constants it refers to. Measured on the 749 modules
of the archive before steiner-six-spectrum (2026-11-22, 16-core aarch64, 15 GiB): 161 s and
6.2 GiB on one thread, where checking each module on top of its own imports took 69 min,
because every module loads Mathlib again. One pass checks on a single thread, though: modules
whose proofs take the kernel minutes each (that entry's certificates) are checked one after the
other, so the cluster still replays per module, on several threads (job/job-steps.sh).

Several listed modules can store the same name: Lean generates some theorems on demand in each
module that needs them (equation lemmas such as `f.eq_def`). Identical copies are replayed once.
Copies that differ must be theorems with the same statement. The kernel accepts a theorem only if
its type is a proposition, and for the kernel any two proofs of a proposition are interchangeable
(proof irrelevance), so it does not matter which copy the other constants see. Every copy is
checked: the first in the pass, each other one under a fresh name against the result. Anything
else stored twice is refused. A theorem the imports already contain with the same statement is
not replayed again (`Lean.Replay` skips it, as in `leanchecker`); any other constant they already
contain is refused by the kernel as a duplicate.

## Per module (`--per-module`)

`replayFromImports` from Lean's `leanchecker`, copied unchanged: each module on top of its own
imports, one task per module, with LEAN_NUM_THREADS bounding the pool. What the cluster's
verify step runs; each thread loads Mathlib for every module it checks.

## Imports (`--imports`)

For each listed module, the files a replay of it reads (its olean parts, found as
`replayFromImports` finds them) and the imports in its compiled header, with their flags, as
JSON. The verify step keys each module by these files and its imports' keys
(job/approvals.mjs), and replays only the modules whose key it has not seen pass before.
The header's imports, not the source's: they are what the replay loads.
-/

-- From LeanChecker.lean (Lean v4.35.0), unchanged.
unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions

/-- The files of a module's olean, found as `replayFromImports` finds them: the exported part,
and the server and private parts where they exist. -/
def oleanFiles (module : Name) : IO (Array System.FilePath) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  return fnames

/-- A module's imports and its constants, read from all parts of its olean (exported, server,
private) as `replayFromImports` reads them: the last ("most private") part subsumes the others. -/
unsafe def readModule (module : Name) : IO (Array Import × ModuleData) := do
  let parts ← readModuleDataParts (← oleanFiles module)
  if h : parts.size = 0 then throw <| IO.userError s!"failed to read the module data of {module}" else
  return (parts[0].1.imports, parts[parts.size - 1].1)

/-- `--imports`: for each listed module, the files a replay of it reads and the imports in its
header (the ones `replayFromImports` loads, with their flags), as JSON. job/approvals.mjs keys
each module by these files and the keys of these imports. Nothing is checked here. -/
unsafe def moduleImports (modules : Array Name) : IO Json := do
  let mut out : Array (String × Json) := #[]
  for m in modules do
    let files ← oleanFiles m
    let parts ← readModuleDataParts files
    if h : parts.size = 0 then throw <| IO.userError s!"failed to read the module data of {m}" else
    out := out.push (m.toString, Json.mkObj [("files", toJson (files.map (·.toString))),
      ("imports", toJson parts[0].1.imports)])
  return Json.mkObj out.toList

structure OnePass where
  constants : Nat
  copies : Nat

/-- The one-pass replay described in the module doc. -/
unsafe def replayOnePass (modules : Array Name) : IO OnePass := do
  let listed : NameSet := modules.foldl (·.insert ·) {}
  -- The trusted imports, each once. Flags are merged: `import all` anywhere loads the module's
  -- private part, and loading more than one module needed never changes what the kernel accepts.
  let mut imports : Array Import := #[]
  let mut importAt : NameMap Nat := {}
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut storedBy : NameMap Name := {}
  let mut copies : Array ConstantInfo := #[]
  for m in modules do
    let (imps, data) ← readModule m
    for i in imps do
      if listed.contains i.module then continue
      match importAt.find? i.module with
      | some k => imports := imports.modify k fun j =>
          { j with importAll := j.importAll || i.importAll, isExported := j.isExported || i.isExported,
                   isMeta := j.isMeta || i.isMeta }
      | none =>
        importAt := importAt.insert i.module imports.size
        imports := imports.push i
    for name in data.constNames, ci in data.constants do
      match newConstants[name]? with
      | none =>
        newConstants := newConstants.insert name ci
        storedBy := storedBy.insert name m
      | some first =>
        if first == ci then continue
        let other := (storedBy.find? name).getD .anonymous
        match first, ci with
        | .thmInfo a, .thmInfo b =>
          unless a.type == b.type && a.levelParams == b.levelParams do
            throw <| IO.userError s!"{name} is stored by {other} and by {m} with different statements"
          copies := copies.push ci
        | _, _ => throw <| IO.userError s!"{name} is stored by {other} and by {m} with different content"
  let (_, s) ← importModulesCore imports |>.run
  let env ← finalizeImport s imports {} 0 false false (isModule := true)
  let kenv ← env.toKernelEnv.replay newConstants
  -- Every other copy of a theorem, under a fresh name, against the result of the pass.
  let mut renamed : Std.HashMap Name ConstantInfo := {}
  for ci in copies, i in [0:copies.size] do
    if let .thmInfo v := ci then
      let n := Name.mkNum (v.name ++ `_lemmata_replay_copy) i
      renamed := renamed.insert n (.thmInfo { v with name := n, all := [n] })
  discard <| kenv.replay renamed
  env.freeRegions
  return { constants := newConstants.size, copies := copies.size }

unsafe def main (args : List String) : IO UInt32 := do
  let (mode, rest) := match args with
    | "--per-module" :: r => ("per-module", r)
    | "--imports" :: r => ("imports", r)
    | r => ("one-pass", r)
  let perModule := mode == "per-module"
  let [listPath] := rest
    | IO.eprintln "usage: lemmata-replay [--per-module | --imports] <file with one module name per line>"; return 2
  initSearchPath (← findSysroot)
  let names := (← IO.FS.readFile listPath).splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (· ≠ "")
  let mut modules : Array Name := #[]
  for n in names do
    let m := n.toName
    if m.isAnonymous then
      IO.eprintln s!"not a module name: {n}"; return 1
    unless modules.contains m do modules := modules.push m
  if modules.isEmpty then
    IO.eprintln "no modules listed: nothing would be checked"; return 1
  if mode == "imports" then
    try
      IO.println (← moduleImports modules).compress
      return 0
    catch e =>
      IO.eprintln s!"cannot read the imports: {e}"; return 1
  if perModule then
    let mut tasks := #[]
    for m in modules do
      tasks := tasks.push (m, ← IO.asTask (replayFromImports m))
    let mut failed := 0
    for (m, t) in tasks do
      match t.get with
      | .ok _ => pure ()
      | .error e => IO.eprintln s!"kernel replay failed in {m}: {e}"; failed := failed + 1
    IO.println s!"lemmata-replay: {modules.size - failed} of {modules.size} modules replayed, one by one"
    return if failed == 0 then 0 else 1
  let t0 ← IO.monoMsNow
  try
    let r ← replayOnePass modules
    let secs := ((← IO.monoMsNow) - t0) / 1000
    let copies := if r.copies == 0 then "" else s!" and {r.copies} differing copies of stored theorems"
    let mods := if modules.size == 1 then "1 module" else s!"{modules.size} modules"
    IO.println s!"lemmata-replay: {mods} replayed in one pass, {r.constants} constants{copies} ({secs} s)"
    return 0
  catch e =>
    IO.eprintln s!"kernel replay failed: {e}"
    return 1
