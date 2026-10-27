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

What it does NOT do: kernel re-checking of proofs. That is `leanchecker`'s job and runs as
a separate step against the same oleans.
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
  pure { root, allowedAxioms := allowed, exports, native }

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

  -- 0. Computation axioms: every axiom defined in the archive whose name has the shape of a
  --    computation claim is examined here; the accepted ones become allowed for the audit
  --    below, everything else stays a disallowed axiom there.
  let mut computations : NameSet := {}
  let mut computationsJson : Array Json := #[]
  let mut computationModule : NameMap Name := {}
  for (c, ci) in env.constants.map₁.toList do
    let some m := moduleOf env c | continue
    unless req.root.isPrefixOf m do continue
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

  let report := Json.mkObj [
    ("tool", "lemmata-check"), ("lean_version", Lean.versionString),
    ("root", toString req.root),
    ("result", if failures.isEmpty then "passed" else "failed"),
    ("modules", toJson (ownMods.map toString)),
    ("declarations_audited", audited),
    ("allowed_axioms", toJson (req.allowedAxioms.map toString)),
    ("archive_axioms", toJson ((sortedNames archiveAxioms).filter (!computations.contains ·) |>.map toString)),
    ("computations", Json.arr computationsJson),
    ("exports", Json.arr exportsJson),
    ("failures", toJson failures)]
  IO.FS.writeFile outPath (report.pretty ++ "\n")
  for f in failures do IO.eprintln s!"FAIL {f}"
  return if failures.isEmpty then 0 else 1
