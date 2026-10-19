import Lean
open Lean

/-!
# lemmata-check

Reads an already-compiled archive and reports what it actually proves. It never elaborates
source: it loads `.olean` files with `loadExts := false`, so no contributor `initialize`
code runs, and it computes axiom dependencies by walking the kernel terms itself rather
than trusting the axiom tables that the (untrusted) build stored inside each `.olean`.

    lemmata-check <request.json> <report.json>

The request names the archive's root module, the allowed axioms, and every exported
declaration from the contribution manifests. The tool exits 0 only if every check passes;
the report is written either way so a failed build can show why.

What it does NOT do: kernel re-checking of proofs. That is `leanchecker`'s job and runs as
a separate step against the same oleans.
-/

structure ExportReq where
  contribution : String
  name : Name
  kind : String
  «namespace» : Name

structure Request where
  root : Name
  allowedAxioms : Array Name
  exports : Array ExportReq

def jStr (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def jArr (j : Json) (k : String) : Except String (Array Json) := j.getObjValAs? (Array Json) k

def parseRequest (j : Json) : Except String Request := do
  let root := (← jStr j "root").toName
  let allowed := (← jArr j "allowed_axioms").filterMap (·.getStr?.toOption) |>.map String.toName
  let exports ← (← jArr j "exports").mapM fun e => do
    pure { contribution := ← jStr e "contribution", name := (← jStr e "name").toName,
           kind := ← jStr e "kind", «namespace» := (← jStr e "namespace").toName }
  pure { root, allowedAxioms := allowed, exports }

/-! ## Axiom collection, independent of stored axiom tables -/

/-- All axioms reachable from `c` through types and values of the kernel constants.
Mirrors the cases of `Lean.CollectAxioms.collect`, minus its `.olean`-stored shortcut. -/
partial def axiomsOf (env : Environment) (c : Name)
    (cache : IO.Ref (NameMap NameSet)) : IO NameSet := do
  if let some s := (← cache.get).find? c then return s
  cache.modify (·.insert c {})       -- cycle sentinel (inductives ↔ constructors)
  let deps (es : List Expr) (extra : List Name := []) : IO NameSet := do
    let mut acc : NameSet := {}
    for e in es do
      for d in e.getUsedConstants do
        for a in (← axiomsOf env d cache) do acc := acc.insert a
    for d in extra do
      for a in (← axiomsOf env d cache) do acc := acc.insert a
    pure acc
  let result ← match env.find? c with
    | some (.axiomInfo v)  => return (← deps [v.type]).insert c |> fun s => s
    | some (.defnInfo v)   => deps [v.type, v.value]
    | some (.thmInfo v)    => deps [v.type, v.value]
    | some (.opaqueInfo v) => deps [v.type, v.value]
    | some (.quotInfo _)   => pure {}
    | some (.ctorInfo v)   => deps [v.type]
    | some (.recInfo v)    => deps [v.type]
    | some (.inductInfo v) => deps [v.type] v.ctors
    | none                 => throw <| IO.userError s!"unknown constant {c}"
  cache.modify (·.insert c result)
  pure result

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor" | .quotInfo _ => "quot"

def sortedNames (s : NameSet) : Array Name := s.toArray.qsort Name.lt

def moduleOf (env : Environment) (c : Name) : Option Name :=
  env.getModuleIdxFor? c |>.map fun i => env.header.moduleNames[i.toNat]!

def modulePath (m : Name) : String :=
  "lean/" ++ (m.components.map toString |> String.intercalate "/") ++ ".lean"

def main (args : List String) : IO UInt32 := do
  let [reqPath, outPath] := args
    | IO.eprintln "usage: lemmata-check <request.json> <report.json>"; return 2
  let req ← IO.ofExcept <| (Json.parse (← IO.FS.readFile reqPath)) >>= parseRequest
  initSearchPath (← findSysroot)
  -- Import every compiled module under the root, found on disk -- not just the umbrella.
  -- A module nothing imports must still be audited.
  let sp ← searchPathRef.get
  let mut onDisk : Array Name := #[]
  for path in (← SearchPath.findAllWithExt sp "olean") do
    if let some m ← searchModuleNameOfFileName path sp then
      if req.root.isPrefixOf m && !onDisk.contains m then onDisk := onDisk.push m
  onDisk := onDisk.qsort Name.lt
  let env ← importModules (onDisk.map ({ module := · })) {} (loadExts := false)
  let allowed : NameSet := req.allowedAxioms.foldl (·.insert ·) {}
  let cache ← IO.mkRef ({} : NameMap NameSet)
  let mut failures : Array String := #[]

  -- 1. Every constant defined anywhere in the archive's own modules, not only the exported
  --    ones: an admitted helper must fail the build even if nothing displays it.
  let ownMods := onDisk
  if ownMods.isEmpty then failures := failures.push s!"no compiled modules under {req.root}"
  let mut audited := 0
  let mut archiveAxioms : NameSet := {}
  for (c, _) in env.constants.map₁.toList do
    let some m := moduleOf env c | continue
    unless req.root.isPrefixOf m do continue
    audited := audited + 1
    for a in (← axiomsOf env c cache) do
      archiveAxioms := archiveAxioms.insert a
      unless allowed.contains a do
        failures := failures.push s!"{c} (in {m}) depends on disallowed axiom {a}"
  if audited == 0 then failures := failures.push "axiom audit covered zero declarations"

  -- 2. Declarations bound in the manifests.
  let mut exportsJson : Array Json := #[]
  for e in req.exports do
    let mut problems : Array String := #[]
    let info? := env.find? e.name
    match info? with
    | none => problems := problems.push "not found in the compiled environment"
    | some ci =>
      if kindOf ci != e.kind then
        problems := problems.push s!"kind is {kindOf ci}, manifest says {e.kind}"
      unless e.«namespace».isPrefixOf e.name do
        problems := problems.push s!"not inside namespace {e.«namespace»}"
      if isPrivateName e.name then problems := problems.push "private declaration"
      match moduleOf env e.name with
      | some m => unless e.«namespace».isPrefixOf m do
          problems := problems.push s!"defined in {m}, outside {e.«namespace»}"
      | none => problems := problems.push "no defining module"
    let axs ← if info?.isSome then pure (sortedNames (← axiomsOf env e.name cache)) else pure #[]
    let bad := axs.filter (!allowed.contains ·)
    unless bad.isEmpty do problems := problems.push s!"disallowed axioms {bad}"
    for p in problems do failures := failures.push s!"{e.name}: {p}"
    let modName := (moduleOf env e.name).getD .anonymous
    exportsJson := exportsJson.push <| Json.mkObj [
      ("contribution", e.contribution), ("name", toString e.name),
      ("kind", match info? with | some ci => kindOf ci | none => e.kind),
      ("module", toString modName), ("source_file", modulePath modName),
      ("type", match info? with | some ci => toString ci.type | none => Json.null),
      ("axioms", toJson (axs.map toString)),
      ("status", if problems.isEmpty then "checked" else "failed"),
      ("problems", toJson problems)]

  let report := Json.mkObj [
    ("tool", "lemmata-check"), ("lean_version", Lean.versionString),
    ("root", toString req.root),
    ("result", if failures.isEmpty then "passed" else "failed"),
    ("modules", toJson (ownMods.map toString)),
    ("declarations_audited", audited),
    ("allowed_axioms", toJson (req.allowedAxioms.map toString)),
    ("archive_axioms", toJson ((sortedNames archiveAxioms).map toString)),
    ("exports", Json.arr exportsJson),
    ("failures", toJson failures)]
  IO.FS.writeFile outPath (report.pretty ++ "\n")
  for f in failures do IO.eprintln s!"FAIL {f}"
  return if failures.isEmpty then 0 else 1
