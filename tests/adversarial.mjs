// Adversarial regression tests for the publishing tools: each case is a copy of the
// repository with one hostile change, and `lemmata.mjs validate` must refuse it (or, for
// the positive controls, accept it). From a security review on 2026-10-22; run by
// tools/check.sh. Usage: node tests/adversarial.mjs
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync, spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TOOL = path.join(REPO, "tools", "lemmata.mjs");
const entry = "implication-composition";          // a real entry to plant changes in
const page = `docs/${entry}/index.md`;

// A fresh copy of the tracked files for each case.
function copy() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lemmata-adv-"));
  const files = execFileSync("git", ["-C", REPO, "ls-files", "-z"]).toString().split("\0").filter(Boolean);
  for (const f of files) { const d = path.join(dir, f); fs.mkdirSync(path.dirname(d), { recursive: true }); fs.copyFileSync(path.join(REPO, f), d); }
  return dir;
}
function validate(dir) {
  const r = spawnSync(process.execPath, [TOOL, "validate"], { env: { ...process.env, LEMMATA_ROOT: dir }, encoding: "utf8" });
  return { ok: r.status === 0, out: (r.stdout + r.stderr).trim() };
}
const append = (dir, f, text) => fs.appendFileSync(path.join(dir, f), text);

let failed = 0;
function expect(name, change, { refused = true, match } = {}) {
  const dir = copy();
  try {
    change(dir);
    const r = validate(dir);
    const good = refused ? !r.ok && (!match || match.test(r.out)) : r.ok;
    console.log(`${good ? "ok  " : "FAIL"} ${name}`);
    if (!good) { failed++; console.log("     " + r.out.split("\n").slice(0, 3).join("\n     ")); }
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
}

// Finding 2: file-reading directives must stay inside the entry's own files.
expect("backtick literalinclude outside the repository",
  (d) => append(d, page, "\n```{literalinclude} ../../../../etc/hosts\n```\n"), { match: /escapes the repository|unsafe path/ });
expect("colon-fenced literalinclude outside the repository",
  (d) => append(d, page, "\n:::{literalinclude} ../../../etc/hosts\n:::\n"), { match: /escapes|unsafe/ });
expect("include with :literal: outside the repository",
  (d) => append(d, page, "\n```{include} ../../../etc/hosts\n:literal:\n```\n"), { match: /escapes|unsafe/ });
expect("absolute include path",
  (d) => append(d, page, "\n:::{include} /etc/hosts\n:::\n"), { match: /unsafe path/ });
expect("include of another entry's files",
  (d) => append(d, page, "\n```{include} ../lagrangian-duality-gap/index.md\n```\n"), { match: /outside this page's files/ });
expect("include of a repository file outside docs/ and the entry's Lean",
  (d) => append(d, page, "\n```{literalinclude} ../../tools/lemmata.mjs\n```\n"), { match: /outside this page's files/ });
expect("four-backtick fence",
  (d) => append(d, page, "\n````{literalinclude} ../../../etc/hosts\n````\n"), { match: /escapes|unsafe/ });
expect("csv-table reading a file outside",
  (d) => append(d, page, "\n```{csv-table}\n:file: ../../../etc/passwd\n```\n"), { match: /escapes|unsafe/ });
expect("figure from a file outside",
  (d) => append(d, page, "\n```{figure} ../../../etc/hosts\n```\n"), { match: /escapes|unsafe/ });
expect("raw html", (d) => append(d, page, "\n```{raw} html\n<script>alert(1)</script>\n```\n"), { match: /not allowed/ });
expect("positive control: the entry's own Lean file is allowed",
  (d) => append(d, page, "\n```{literalinclude} ../../lean/Lemmata/ImplicationComposition/Main.lean\n```\n"), { refused: false });
expect("positive control: a web figure is allowed",
  (d) => append(d, page, "\n```{figure} https://example.org/a.png\n```\n"), { refused: false });

// Finding 3: an entry id that names an Object.prototype property.
// A complete, consistent entry under that id: only the id itself may be the problem.
function renameEntry(d, to) {
  fs.renameSync(path.join(d, "docs", entry), path.join(d, "docs", to));
  for (const f of [`docs/${to}/contribution.yml`, `docs/${to}/index.md`]) {
    const p = path.join(d, f); fs.writeFileSync(p, fs.readFileSync(p, "utf8").replaceAll(entry, to));
  }
}
expect("positive control: a consistently renamed entry is accepted", (d) => renameEntry(d, "composition-of-implications"), { refused: false });
for (const id of ["constructor", "prototype", "hasownproperty", "valueof", "tostring"])
  expect(`entry id '${id}' is refused (it names an Object.prototype property)`, (d) => renameEntry(d, id), { match: /reserved/ });

// Finding 1: the Lean statement shown next to a result must be that declaration's, found
// by syntax, not text: not one inside a comment or string, not a same-named declaration
// in another namespace, and a definition must not be cut at a blank line.
const SRC = fs.readFileSync(TOOL, "utf8");
const leanStatement = new Function("fs", "path", "ROOT",
  SRC.slice(SRC.indexOf("const DECL_KW"), SRC.indexOf("function forgeLinks")) + "; return leanStatement;");
function statementCase(name, lean, fullName, check) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lemmata-adv-"));
  try {
    fs.writeFileSync(path.join(dir, "Main.lean"), lean);
    const st = leanStatement(fs, path, dir)("Main.lean", fullName);
    const good = check(st);
    console.log(`${good ? "ok  " : "FAIL"} ${name}`);
    if (!good) { failed++; console.log("     got: " + JSON.stringify(st?.text ?? st)); }
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
}
statementCase("a decoy theorem in a block comment is not shown",
  "namespace Lemmata.X\n/-\ntheorem main : 1 = 2\n-/\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a decoy in a nested block comment is not shown",
  "namespace Lemmata.X\n/- outer /- inner -/\ntheorem main : 1 = 2\n-/\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a decoy in a line comment is not shown",
  "namespace Lemmata.X\n-- theorem main : 1 = 2\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a decoy in a string is not shown",
  "namespace Lemmata.X\ndef s : String := \"\ntheorem main : 1 = 2\"\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a same-named theorem in another namespace is not shown",
  "namespace Lemmata.Other\ntheorem main : 1 = 2 := sorry\nend Lemmata.Other\nnamespace Lemmata.X\ntheorem main : 1 = 1 := rfl\nend Lemmata.X\n",
  "Lemmata.X.main", (st) => st && /1 = 1/.test(st.text) && !/1 = 2/.test(st.text));
statementCase("a definition is not cut at a blank line",
  "namespace Lemmata.X\ndef f (n : Nat) : Nat :=\n  n + 1\n\n  -- still the body after a blank line\n  |> id\ntheorem t : True := trivial\nend Lemmata.X\n",
  "Lemmata.X.f", (st) => st && /\|> id/.test(st.text) && !/theorem t/.test(st.text));
statementCase("a missing declaration gives no statement (not some other one)",
  "namespace Lemmata.X\n-- theorem gone : 1 = 2\ntheorem other : True := trivial\nend Lemmata.X\n",
  "Lemmata.X.gone", (st) => st === null);

// Computations (2026-10-26): native_decide and friends only in an entry that declares
// native_computation: true; hand-written axioms and swapped-in compiled code nowhere.
const lean = `lean/Lemmata/ImplicationComposition/Main.lean`, mf = `docs/${entry}/contribution.yml`;
const addLean = (d, text) => append(d, lean.replace("Main.lean", "Extra.lean"), "module\n\npublic section\n\nnamespace Lemmata.ImplicationComposition\n" + text + "\nend Lemmata.ImplicationComposition\n");
const withUmbrella = (d) => fs.writeFileSync(path.join(d, "lean/Lemmata.lean"),
  fs.readFileSync(path.join(d, "lean/Lemmata.lean"), "utf8").replace("Lemmata.ImplicationComposition.Main", "Lemmata.ImplicationComposition.Extra\npublic import Lemmata.ImplicationComposition.Main"));
const flag = (d) => append(d, mf, "native_computation: true\n");
expect("native_decide without native_computation: true",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by native_decide"); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("decide +native without native_computation: true",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by decide +native"); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("bv_decide without native_computation: true",
  (d) => { addLean(d, "theorem t : True := by bv_decide"); withUmbrella(d); }, { match: /without `native_computation: true`/ });
expect("positive control: native_decide in an entry with native_computation: true",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by native_decide"); withUmbrella(d); flag(d); }, { refused: false });
expect("positive control: native_decide in a comment or string is no computation",
  (d) => { addLean(d, "-- by native_decide\n/- native_decide -/\ndef s : String := \"native_decide\""); withUmbrella(d); }, { refused: false });
expect("positive control: plain decide and decide +kernel need no flag",
  (d) => { addLean(d, "theorem t : 2 + 2 = 4 := by decide\ntheorem u : 2 + 2 = 4 := by decide +kernel"); withUmbrella(d); }, { refused: false });
expect("native_decide in lean/Lemmata/Shared",
  (d) => append(d, "lean/Lemmata/Shared/Basic.lean", "\ntheorem lemmata_shared_t : 2 + 2 = 4 := by native_decide\n"), { match: /lean\/Lemmata\/Shared must stay kernel-checked/ });
expect("a hand-written axiom, even in a flagged entry",
  (d) => { addLean(d, "axiom fake : (1 : Nat) = 2"); withUmbrella(d); flag(d); }, { match: /an axiom is not allowed/ });
expect("an axiom named like a computation",
  (d) => { addLean(d, "axiom t._native.native_decide.ax_1_1 : decide ((1 : Nat) = 2) = true"); withUmbrella(d); flag(d); }, { match: /an axiom is not allowed/ });
expect("@[implemented_by]",
  (d) => { addLean(d, "def f (n : Nat) : Nat := n\n@[implemented_by f] def g (n : Nat) : Nat := n + 1"); withUmbrella(d); flag(d); }, { match: /implemented_by.*not allowed/ });
expect("@[extern] after another attribute",
  (d) => { addLean(d, "@[inline, extern \"lean_nat_add\"] def h (n : Nat) : Nat := n"); withUmbrella(d); }, { match: /extern.*not allowed/ });
expect("native_computation must be true", (d) => append(d, mf, "native_computation: false\n"), { match: /must be true or left out/ });

console.log(failed ? `\n${failed} adversarial case(s) FAILED` : "\nall adversarial cases passed");
process.exit(failed ? 1 : 0);
