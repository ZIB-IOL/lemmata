// Tests for partial checks (tools/check.sh --entry / --changed): what `lemmata.mjs scope`
// covers for a change, the request it leads to, and how the render shows entries a partial
// check did not cover. No Lean is compiled. Run by tools/check.sh. Usage: node tests/scope.mjs
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync, spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TOOL = path.join(REPO, "tools", "lemmata.mjs");

let failed = 0;
const check = (name, ok, detail = "") => {
  console.log(`${ok ? "ok  " : "FAIL"} ${name}`);
  if (!ok) { failed++; if (detail) console.log("     " + String(detail).split("\n").slice(0, 4).join("\n     ")); }
};
const run = (root, args) => {
  const r = spawnSync(process.execPath, [TOOL, ...args], { env: { ...process.env, LEMMATA_ROOT: root }, encoding: "utf8" });
  let json = null; try { json = JSON.parse(r.stdout); } catch { }
  return { ok: r.status === 0, json, out: (r.stdout + r.stderr).trim() };
};
const scope = (root, ...args) => run(root, ["scope", ...args]);
function copy() {                                   // the tracked files, without git
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lemmata-scope-"));
  const files = execFileSync("git", ["-C", REPO, "ls-files", "-z"]).toString().split("\0").filter(Boolean);
  for (const f of files) { const d = path.join(dir, f); fs.mkdirSync(path.dirname(d), { recursive: true }); fs.copyFileSync(path.join(REPO, f), d); }
  return dir;
}

// What can affect every entry means the full check; what affects no Lean result, none.
for (const f of ["lean/lakefile.toml", "lean/lean-toolchain", "lean/lake-manifest.json", "checker/Main.lean", "tools/lemmata.mjs", "lean/Lemmata/Loose.lean"]) {
  const r = scope(REPO, "--files", f);
  check(`a change to ${f} means the full check`, r.ok && r.json?.mode === "full", r.out);
}
for (const f of ["docs/references.bib", "docs/about.md", "README.md", "tests/browser.mjs", "lean/Lemmata.lean"]) {
  const r = scope(REPO, "--files", f);
  check(`a change to ${f} affects no Lean module`, r.ok && r.json?.mode === "none", r.out);
}
{
  const a = scope(REPO, "--entry", "implication-composition"), b = scope(REPO, "--entry", "ImplicationComposition");
  check("--entry takes an id or a LeanName", a.ok && b.ok && JSON.stringify(a.json) === JSON.stringify(b.json) && a.json.entries.includes("implication-composition"), a.out + b.out);
  const p = scope(REPO, "--files", "docs/implication-composition/index.md");
  check("a change to an entry's prose covers that entry", p.ok && p.json?.mode === "scoped" && p.json.entries.includes("implication-composition"), p.out);
  const u = scope(REPO, "--entry", "no-such-entry");
  check("an unknown entry is refused", !u.ok && /no entry "no-such-entry"/.test(u.out), u.out);
}

// A controlled chain in a copy: TestC imports TestB, which imports TestA, which imports Shared.
const dir = copy();
try {
  for (const [id, lean] of [["test-a", "TestA"], ["test-b", "TestB"], ["test-c", "TestC"]]) {
    const r = run(dir, ["new", id, lean, "math.LO"]);
    if (!r.ok) throw new Error(`scaffold ${id}: ${r.out}`);
    fs.appendFileSync(path.join(dir, "docs", id, "contribution.yml"), "abstract: A test entry.\n");   // a placeholder to fill
  }
  const addImport = (lean, imp) => {
    const f = path.join(dir, "lean/Lemmata", lean, "Main.lean");
    fs.writeFileSync(f, fs.readFileSync(f, "utf8").replace("public import Mathlib.Logic.Function.Basic", `public import Mathlib.Logic.Function.Basic\npublic import ${imp}`));
  };
  addImport("TestA", "Lemmata.Shared.Basic"); addImport("TestB", "Lemmata.TestA.Main"); addImport("TestC", "Lemmata.TestB.Main");
  // a module nothing imports, in TestC
  fs.writeFileSync(path.join(dir, "lean/Lemmata/TestC/Extra.lean"), "module\n\npublic section\n\nnamespace Lemmata.TestC\ntheorem extra : True := trivial\nend Lemmata.TestC\n");
  const entriesOf = (r) => (r.json?.entries ?? []).filter((e) => e.startsWith("test-")).join(",");
  const a = scope(dir, "--files", "lean/Lemmata/TestA/Main.lean");
  check("a change covers every entry that imports it, directly or not", a.ok && entriesOf(a) === "test-a,test-b,test-c", a.out);
  const b = scope(dir, "--files", "docs/test-b/contribution.yml");
  check("... but not the entries it imports", b.ok && entriesOf(b) === "test-b,test-c" && !b.json.modules.some((m) => m.startsWith("Lemmata.TestA.")), b.out);
  const c = scope(dir, "--files", "lean/Lemmata/TestC/Extra.lean");
  check("a covered entry brings all its modules, also those nothing imports", c.ok && entriesOf(c) === "test-c" &&
    ["Lemmata.TestC.Main", "Lemmata.TestC.Extra"].every((m) => c.json.modules.includes(m)), c.out);
  const s = scope(dir, "--entry", "Shared");
  check("a change to lean/Lemmata/Shared covers the entries that use it", s.ok && entriesOf(s) === "test-a,test-b,test-c" && s.json.dirs.includes("Shared"), s.out);
  const gone = scope(dir, "--files", "lean/Lemmata/Removed/Main.lean");
  check("a removed directory covers nothing but itself", gone.ok && gone.json?.mode === "scoped" && entriesOf(gone) === "", gone.out);

  // The request of a partial check: only its exports, exactly its modules, every native entry.
  fs.writeFileSync(path.join(dir, "scope.json"), JSON.stringify(b.json));
  const q = run(dir, ["request", path.join(dir, "req.json"), "--scope", path.join(dir, "scope.json")]);
  const req = q.ok ? JSON.parse(fs.readFileSync(path.join(dir, "req.json"), "utf8")) : null;
  const full = run(dir, ["request", path.join(dir, "req-full.json")]);
  const reqFull = full.ok ? JSON.parse(fs.readFileSync(path.join(dir, "req-full.json"), "utf8")) : null;
  check("a partial request has only its entries' exports and exactly its modules",
    req && req.exports.length > 0 && req.exports.every((e) => ["test-b", "test-c"].includes(e.contribution)) &&
    JSON.stringify(req.modules) === JSON.stringify(b.json.modules) && JSON.stringify(req.scope) === JSON.stringify(b.json.entries), q.out);
  check("... and still names every entry that may use computations", req && reqFull && JSON.stringify(req.native) === JSON.stringify(reqFull.native));
  check("the full request is unchanged: no modules, no scope", reqFull && !("modules" in reqFull) && !("scope" in reqFull));

  // The render of a partial check: covered entries as reported, the others not verified.
  const report = { result: "passed", lean_version: "4.35.0", scope: ["test-b"], computations: [],
    exports: [{ contribution: "test-b", name: "Lemmata.TestB.main", kind: "theorem", status: "checked", computations: [],
      module: "Lemmata.TestB.Main", source_file: "lean/Lemmata/TestB/Main.lean", type: "True", axioms: [], problems: [] }] };
  fs.writeFileSync(path.join(dir, "report.json"), JSON.stringify(report));
  const p = run(dir, ["prepare", path.join(dir, "report.json"), "--commit", "c".repeat(12)]);
  const panel = (id) => { try { return fs.readFileSync(path.join(dir, "docs/_generated/verification", `${id}.md`), "utf8"); } catch { return ""; } };
  check("render: an entry the partial check covered shows its result", p.ok && /kernel-checked/.test(panel("test-b")) && !/not verified/.test(panel("test-b")), p.out);
  check("render: an entry it did not cover is shown as not verified, not as failed",
    p.ok && /not verified/.test(panel("test-c")) && !/✗|failed/i.test(panel("test-c")) && /not verified/.test(panel("implication-composition")), panel("test-c").slice(0, 300));
} finally { fs.rmSync(dir, { recursive: true, force: true }); }

console.log(failed ? `\n${failed} scope case(s) FAILED` : "\nall scope cases passed");
process.exit(failed ? 1 : 0);
