import Lean
open Lean

/-!
# lemmata-check

Reads an already-compiled archive and reports what it actually proves. It never elaborates
source: it loads `.olean` files with `loadExts := false`, so no contributor `initialize`
code runs, and it computes axiom dependencies by walking the kernel terms itself rather
than trusting the axiom tables that the (untrusted) build stored inside each `.olean`.

    lemmata-check <request.json> <report.json>

The request names the archive's root module, the allowed axioms, every exported
declaration from the contribution manifests, and which entries declare
`native_computation: true`. The tool exits 0 only if every check passes; the report is
written either way so a failed build can show why.

Without `modules` in the request (the cluster), every compiled module under the root found
on disk is imported and audited. A partial local check (`tools/check.sh --entry` or `--changed`
in the content repository) names its modules exactly in `modules`: only those are audited,
what they import from other entries comes along as it is, and the request's `scope` (the
entries it covers) is copied into the report, so the rendered site can tell which entries
this run did not check.

## Namespaces

Every public declaration of an entry's modules must lie in the entry's namespace,
`Lemmata.<LeanName>` (`Lemmata.Shared` for the shared helpers). Private declarations,
internal ones (`_proof_1`, `match_1`, ...) and the names Lean reserves for what it generates
on demand (`f.eq_def`, `f.congr_simp`, ...; `isReservedName`) are exempt. So no two entries
can declare the same name, which would only show when the umbrella imports both; that also
makes a partial local check, which never builds the umbrella, equivalent to the full one.

## Computations (`native_computation: true`)

`native_decide` (also `decide +native`, `bv_decide`) has the compiler run a Boolean
expression during the build and, if it evaluates to `true`, adds an axiom `e = true`
named `<declaration>._native.<tactic>.ax_<n>_<m>`. The kernel never checks that claim, and
nobody re-runs it. An entry may rely on such computations only if its manifest opts in, and
then a computation axiom is accepted only if:

- it is named as Lean's tactics name them, with no universe parameters, and states exactly
  `b = true` for a closed `Bool` (any other statement is a plain custom axiom and refused);
- it is defined in a module of an entry that declared `native_computation: true` (never in
  `Lemmata.Shared`, which has no manifest).

That is deliberately all. Whether a claim really came from Lean's tactic is not checked:
a contributor could produce one by other means, and the build that compiles the source is
untrusted anyway (an earlier version matched source positions and restricted metaprogramming,
and kept being bypassed; removed 2026-10-27). What protects readers is the label: a result
that depends on any computation is never shown as kernel-checked, every claim is listed with
its statement and source line, and the opt-in is a reviewed decision. The report lists every
accepted computation and, per export, the computations it relies on.

What it does NOT do: kernel re-checking of proofs. That is `lemmata-replay`'s job
(Replay.lean: the kernel replay of an exact module list) and runs as a separate step
against the same oleans.
-/

structure ExportReq where
  contribution : String
  name : Name
  kind : String
  «namespace» : Name

/-- An entry that declared `native_computation: true`. -/
structure NativeReq where
  contribution : String
  «namespace» : Name

structure Request where
  root : Name
  allowedAxioms : Array Name
  exports : Array ExportReq
  native : Array NativeReq
  /-- Exactly the modules to import and audit (a partial local check); none: all on disk. -/
  modules : Option (Array Name) := none
  /-- The entries a partial local check covers, copied into the report. -/
  scope : Option (Array String) := none

def jStr (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def jArr (j : Json) (k : String) : Except String (Array Json) := j.getObjValAs? (Array Json) k

def parseRequest (j : Json) : Except String Request := do
  let root := (← jStr j "root").toName
  let allowed := (← jArr j "allowed_axioms").filterMap (·.getStr?.toOption) |>.map String.toName
  let exports ← (← jArr j "exports").mapM fun e => do
    pure { contribution := ← jStr e "contribution", name := (← jStr e "name").toName,
           kind := ← jStr e "kind", «namespace» := (← jStr e "namespace").toName }
  -- Optional, so an older request (no computations anywhere) still parses.
  let nativeJs := (j.getObjValAs? (Array Json) "native").toOption.getD #[]
  let native ← nativeJs.mapM fun n => do
    pure { contribution := ← jStr n "contribution", «namespace» := (← jStr n "namespace").toName }
  -- Optional too: only a partial local check sends them.
  let modules := (j.getObjValAs? (Array String) "modules").toOption.map (·.map String.toName)
  let scope := (j.getObjValAs? (Array String) "scope").toOption
  pure { root, allowedAxioms := allowed, exports, native, modules, scope }

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
  -- Every branch must produce a value, never `return`: a `return` here leaves the cycle
  -- sentinel `{}` in the cache, and every later lookup of this constant then reports no
  -- axioms at all. That lost axioms and computations depending on traversal order
  -- (reported 2026-10-26: 18 of 40 computation-backed results listed none).
  let result ← match env.find? c with
    | some (.axiomInfo v)  => pure ((← deps [v.type]).insert c)
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

/-! ## Computation axioms -/

/-- The tactics whose auxiliary axioms are computation claims (`Lean.Meta.nativeEqTrue`). -/
def nativeTactics : List String := ["native_decide", "decide", "bv_decide"]

/-- `t._native.<tactic>.ax_<n>[_<m>]` (after removing a private prefix): the declaration
`t` it belongs to and the tactic, if the name has exactly that shape. -/
def nativeAxiomParts (n : Name) : Option (Name × String) := do
  let n := (privateToUserName? n).getD n
  let .str (.str (.str decl "_native") tac) ax := n | none
  guard (nativeTactics.contains tac && ax.startsWith "ax_" && !decl.isAnonymous)
  let digits := (ax.drop 3).toString.splitOn "_"
  guard (!digits.isEmpty && digits.all fun d => !d.isEmpty && d.all Char.isDigit)
  pure (decl, tac)

/-- The statement a computation axiom must have: `@Eq Bool lhs Bool.true` with `lhs` closed. -/
def isComputationClaim (ty : Expr) : Bool :=
  ty.isAppOfArity ``Eq 3 && ty.appFn!.appFn!.appArg!.isConstOf ``Bool &&
    ty.appArg!.isConstOf ``Bool.true && !ty.appFn!.appArg!.hasLooseBVars &&
    !ty.appFn!.appArg!.hasFVar && !ty.appFn!.appArg!.hasMVar

/-! ## Namespaces -/

/-- The namespace the public declarations of module `m` belong in: `Lemmata.<Entry>` for a
module `Lemmata.<Entry>.…` (`Lemmata.Shared` for the shared helpers). The umbrella has none. -/
def entryNamespace? (root m : Name) : Option Name :=
  let rc := root.components
  let mc := m.components
  if rc.length < mc.length && mc.take rc.length == rc then
    some ((mc.take (rc.length + 1)).foldl (· ++ ·) .anonymous)
  else none

/-- Declarations exempt from the namespace rule: private ones (unique to their module),
internal ones (`_proof_1`, `match_1`, ...), and the names Lean reserves for what it generates on
demand, in any module that needs it (`f.eq_def`, `f.congr_simp`, ...). -/
def namespaceExempt (env : Environment) (c : Name) : Bool :=
  isPrivateName c || c.isInternalDetail || isReservedName env c

def main (args : List String) : IO UInt32 := do
  let [reqPath, outPath] := args
    | IO.eprintln "usage: lemmata-check <request.json> <report.json>"; return 2
  let req ← IO.ofExcept <| (Json.parse (← IO.FS.readFile reqPath)) >>= parseRequest
  let t0 ← IO.monoMsNow                -- the time of each phase goes into the report
  initSearchPath (← findSysroot)
  let mut failures : Array String := #[]
  let mut ownMods : Array Name := #[]
  if let some listed := req.modules then
    -- A partial local check names its modules exactly; every one must be compiled.
    for m in listed do
      let compiled ← try (← findOLean m).pathExists catch _ => pure false
      if !req.root.isPrefixOf m then failures := failures.push s!"{m} is not under {req.root}"
      else if !compiled then failures := failures.push s!"{m} is listed but has no compiled .olean"
      else if !ownMods.contains m then ownMods := ownMods.push m
  else
    -- Import every compiled module under the root, found on disk -- not just the umbrella.
    -- A module nothing imports must still be audited.
    let sp ← searchPathRef.get
    for path in (← SearchPath.findAllWithExt sp "olean") do
      if let some m ← searchModuleNameOfFileName path sp then
        if req.root.isPrefixOf m && !ownMods.contains m then ownMods := ownMods.push m
  ownMods := ownMods.qsort Name.lt
  let own : NameSet := ownMods.foldl (·.insert ·) {}
  let env ← importModules (ownMods.map ({ module := · })) {} (loadExts := false)
  let allowed : NameSet := req.allowedAxioms.foldl (·.insert ·) {}
  let cache ← IO.mkRef ({} : NameMap NameSet)
  -- The constants of the archive's modules (under the root), module by module from each
  -- module's own list, keeping exactly those the environment attributes to that module -- the
  -- same constants as going through all of `env.constants` and asking each for its module,
  -- without touching every name of Mathlib in the mapped oleans (that took a minute, 2026-11-26).
  let archiveConsts : Array (Name × ConstantInfo × Name) := Id.run do
    let mut out := #[]
    for h : i in [0:env.header.moduleNames.size] do
      let m := env.header.moduleNames[i]
      unless req.root.isPrefixOf m do continue
      let some data := env.header.moduleData[i]? | continue
      for c in data.constNames do
        if moduleOf env c == some m then
          if let some ci := env.find? c then out := out.push (c, ci, m)
    return out
  let tImport ← IO.monoMsNow

  -- 0. Computation axioms: every axiom defined in the archive whose name has the shape of a
  --    computation claim is examined here; the accepted ones become allowed for the audit
  --    below, everything else stays a disallowed axiom there. (All archive modules present,
  --    also those a partial check only imports: its entries may rely on their computations.)
  let mut computations : NameSet := {}
  let mut computationsJson : Array Json := #[]
  let mut computationModule : NameMap Name := {}
  for (c, ci, m) in archiveConsts do
    let .axiomInfo v := ci | continue
    let some (decl, tac) := nativeAxiomParts c | continue
    let file := modulePath m
    -- Where the build recorded it, for the page's link to the source line (not a check).
    let line? := (declRangeExt.find? (level := .server) env c).map (·.range.pos.line)
    let entry? := req.native.find? (·.«namespace».isPrefixOf m)
    let mut why : Array String := #[]
    unless v.levelParams.isEmpty do why := why.push "has universe parameters"
    unless isComputationClaim v.type do why := why.push "does not state `<Bool expression> = true`"
    if entry?.isNone then
      why := why.push s!"is in {m}, which belongs to no entry with `native_computation: true`"
    if why.isEmpty then
      computations := computations.insert c
      computationModule := computationModule.insert c m
      computationsJson := computationsJson.push <| Json.mkObj [
        ("name", toString c), ("declaration", toString ((privateToUserName? decl).getD decl)),
        ("tactic", if tac == "decide" then "decide +native" else tac),
        ("contribution", (entry?.map (·.contribution)).getD ""),
        ("module", toString m), ("source_file", file), ("line", toJson line?),
        ("claim", toString v.type.appFn!.appArg!)]
    else
      failures := failures.push s!"{c} (in {m}) is not an accepted computation: it {", ".intercalate why.toList}"
  let mut allowed := allowed
  for c in computations do allowed := allowed.insert c
  let tComputations ← IO.monoMsNow

  -- 1. Every constant defined anywhere in the archive's own modules, not only the exported
  --    ones: an admitted helper must fail the build even if nothing displays it.
  if ownMods.isEmpty then failures := failures.push s!"no compiled modules under {req.root}"
  let mut audited := 0
  let mut archiveAxioms : NameSet := {}
  let mut outside : Array (Name × Name × Name) := #[]
  for (c, _, m) in archiveConsts do
    unless own.contains m do continue
    audited := audited + 1
    for a in (← axiomsOf env c cache) do
      archiveAxioms := archiveAxioms.insert a
      unless allowed.contains a do
        failures := failures.push s!"{c} (in {m}) depends on disallowed axiom {a}"
    -- and every public declaration lies in its entry's namespace ("Namespaces" above)
    if let some ns := entryNamespace? req.root m then
      unless ns.isPrefixOf c || namespaceExempt env c do outside := outside.push (c, m, ns)
  if audited == 0 then failures := failures.push "axiom audit covered zero declarations"
  for (c, m, ns) in outside.qsort (fun a b => a.1.lt b.1) do
    failures := failures.push (s!"{c} (in {m}) is declared outside {ns}: put it inside `namespace {ns}` " ++
      "or make it private, so that no two entries can declare the same name")
  let tAudit ← IO.monoMsNow

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
    -- The computations it relies on, each with the module that defines it.
    let uses := axs.filter computations.contains |>.map fun a =>
      Json.mkObj [("name", toString a), ("module", toString ((computationModule.find? a).getD .anonymous))]
    for p in problems do failures := failures.push s!"{e.name}: {p}"
    let modName := (moduleOf env e.name).getD .anonymous
    exportsJson := exportsJson.push <| Json.mkObj [
      ("contribution", e.contribution), ("name", toString e.name),
      ("kind", match info? with | some ci => kindOf ci | none => e.kind),
      ("module", toString modName), ("source_file", modulePath modName),
      ("type", match info? with | some ci => toString ci.type | none => Json.null),
      ("axioms", toJson ((axs.filter (!computations.contains ·)).map toString)),
      ("computations", Json.arr uses),
      ("status", if problems.isEmpty then "checked" else "failed"),
      ("problems", toJson problems)]
  let tExports ← IO.monoMsNow
  -- What the axiom walk visited, in the archive and outside it (Mathlib, Lean, ...).
  let mut walkedArchive : Nat := 0
  let mut walkedOther : Nat := 0
  for (c, _) in (← cache.get).toList do
    if (moduleOf env c).any (req.root.isPrefixOf ·) then walkedArchive := walkedArchive + 1
    else walkedOther := walkedOther + 1
  let secs (a b : Nat) : Json := toJson ((b - a).toFloat / 1000)

  let report := Json.mkObj <| ([
    ("tool", "lemmata-check"), ("lean_version", Lean.versionString),
    ("root", toString req.root),
    ("result", if failures.isEmpty then "passed" else "failed"),
    ("modules", toJson (ownMods.map toString)),
    ("declarations_audited", audited),
    ("allowed_axioms", toJson (req.allowedAxioms.map toString)),
    ("archive_axioms", toJson ((sortedNames archiveAxioms).filter (!computations.contains ·) |>.map toString)),
    ("computations", Json.arr computationsJson),
    ("exports", Json.arr exportsJson),
    ("failures", toJson failures),
    ("seconds", Json.mkObj [("import", secs t0 tImport), ("computations", secs tImport tComputations),
      ("audit", secs tComputations tAudit), ("exports", secs tAudit tExports)]),
    ("walked", Json.mkObj [("archive", toJson walkedArchive), ("other", toJson walkedOther)])] : List (String × Json)) ++
    -- Only in a partial local check: the entries it covered (the others were not checked).
    (match req.scope with | some s => [("scope", toJson s)] | none => [])
  IO.FS.writeFile outPath (report.pretty ++ "\n")
  for f in failures do IO.eprintln s!"FAIL {f}"
  return if failures.isEmpty then 0 else 1
