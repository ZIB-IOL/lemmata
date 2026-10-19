#!/usr/bin/env node
// Repository tooling for Lemmata. One file, no dependencies besides `yaml`, so the
// cluster's build Job can run the same code a contributor runs locally.
//
//   node tools/lemmata.mjs validate            structure, manifests, pairing, snippets, umbrella
//   node tools/lemmata.mjs umbrella [--write]  check (or regenerate) lean/Lemmata.lean
//   node tools/lemmata.mjs request <out.json>  verifier request built from the manifests
//   node tools/lemmata.mjs prepare <report.json> [--commit SHA] [--source-url URL]
//                                              generated pages + docs/myst.runtime.yml
//   node tools/lemmata.mjs new <id> <LeanName> scaffold a new contribution
//
// Exit status is non-zero on any problem; every problem is printed, not just the first.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import YAML from "yaml";

// LEMMATA_ROOT lets the cluster run its own (trusted) copy of this file against a
// checkout somewhere else; locally the repository is the file's parent directory.
const ROOT = path.resolve(process.env.LEMMATA_ROOT ?? path.join(path.dirname(fileURLToPath(import.meta.url)), ".."));
const DOCS = path.join(ROOT, "docs");
const LEAN = path.join(ROOT, "lean");
const LIB = "Lemmata";
const ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"];
const POLICY_ID = "lemmata-verification-v1";

// Directories in docs/ and lean/Lemmata/ that are infrastructure, not contributions.
const RESERVED_DOCS = new Set(["_static", "_generated", "_build", "_releases", "_status",
  "index", "healthz", "readyz", "node_modules"]);
const RESERVED_LEAN = new Set(["Shared"]);
const MANIFEST_KEYS = new Set(["schema_version", "id", "lean_namespace", "pages", "exports"]);
const EXPORT_KEYS = new Set(["name", "kind", "page", "label"]);
const KINDS = new Set(["theorem", "definition"]);
const ID_RE = /^[a-z][a-z0-9]*(-[a-z0-9]+)*$/;
const LEAN_COMPONENT_RE = /^[A-Z][A-Za-z0-9]*$/;
const LABEL_RE = /^[a-z][a-z0-9-]*$/;

const problems = [];
const fail = (msg) => problems.push(msg);

function finish(okMessage) {
  if (problems.length) {
    for (const p of problems) console.error(`FAIL ${p}`);
    console.error(`${problems.length} problem(s)`);
    process.exit(1);
  }
  if (okMessage) console.log(okMessage);
}

// Refuse anything that is not a plain file/directory inside the repo: no symlinks, no
// traversal. Used for every path a manifest or page can name.
function safeRel(base, rel, what) {
  if (typeof rel !== "string" || !rel || path.isAbsolute(rel) || rel.includes("\\")) {
    fail(`${what}: unsafe path ${JSON.stringify(rel)}`); return null;
  }
  const abs = path.resolve(base, rel);
  if (!abs.startsWith(ROOT + path.sep)) { fail(`${what}: ${rel} escapes the repository`); return null; }
  let p = abs;
  while (p !== ROOT) {
    try { if (fs.lstatSync(p).isSymbolicLink()) { fail(`${what}: ${rel} goes through a symlink`); return null; } }
    catch { break; }
    p = path.dirname(p);
  }
  return abs;
}

function listDirs(dir) {
  return fs.readdirSync(dir, { withFileTypes: true })
    .filter((d) => d.isDirectory() && !d.name.startsWith(".")).map((d) => d.name).sort();
}

function walk(dir, ext, out = []) {
  for (const d of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, d.name);
    if (d.isSymbolicLink()) fail(`symlink not allowed: ${path.relative(ROOT, p)}`);
    else if (d.isDirectory()) walk(p, ext, out);
    else if (d.name.endsWith(ext)) out.push(p);
  }
  return out;
}

// ---------------------------------------------------------------------------- manifests

function loadManifests() {
  const manifests = [];
  const seen = { ids: new Map(), ns: new Map(), labels: new Map(), lower: new Map() };
  for (const dir of listDirs(DOCS)) {
    if (RESERVED_DOCS.has(dir)) continue;
    const where = `docs/${dir}`;
    if (!ID_RE.test(dir)) { fail(`${where}: directory name is not a lowercase kebab-case id`); continue; }
    const mfPath = path.join(DOCS, dir, "contribution.yml");
    if (!fs.existsSync(mfPath)) { fail(`${where}: missing contribution.yml`); continue; }
    let m;
    try { m = YAML.parse(fs.readFileSync(mfPath, "utf8"), { uniqueKeys: true }); }
    catch (e) { fail(`${where}/contribution.yml: ${e.message}`); continue; }
    if (!m || typeof m !== "object") { fail(`${where}/contribution.yml: not a mapping`); continue; }
    for (const k of Object.keys(m)) if (!MANIFEST_KEYS.has(k)) fail(`${where}/contribution.yml: unknown field ${k}`);
    if (m.schema_version !== 1) fail(`${where}/contribution.yml: schema_version must be 1`);
    if (m.id !== dir) fail(`${where}/contribution.yml: id ${JSON.stringify(m.id)} does not match directory`);

    const ns = String(m.lean_namespace ?? "");
    const comps = ns.split(".");
    if (comps.length !== 2 || comps[0] !== LIB || !LEAN_COMPONENT_RE.test(comps[1]) || RESERVED_LEAN.has(comps[1]))
      fail(`${where}/contribution.yml: lean_namespace must be ${LIB}.<UpperCamel>, got ${JSON.stringify(ns)}`);
    const leanDir = comps[1] ? path.join(LEAN, LIB, comps[1]) : null;
    if (leanDir && !fs.existsSync(path.join(leanDir, "Main.lean")))
      fail(`${where}: lean/${LIB}/${comps[1]}/Main.lean does not exist`);

    for (const [key, map, val] of [["id", seen.ids, m.id], ["lean_namespace", seen.ns, ns]]) {
      if (map.has(val)) fail(`${where}: ${key} ${val} already used by ${map.get(val)}`);
      map.set(val, where);
    }
    const lower = (comps[1] ?? "").toLowerCase();
    if (seen.lower.has(lower)) fail(`${where}: Lean directory ${comps[1]} collides case-insensitively with ${seen.lower.get(lower)}`);
    seen.lower.set(lower, where);

    const pages = Array.isArray(m.pages) ? m.pages : [];
    if (pages[0] !== "index.md") fail(`${where}/contribution.yml: pages must start with index.md`);
    const pageSet = new Set();
    for (const p of pages) {
      if (typeof p !== "string" || !p.endsWith(".md")) { fail(`${where}: page ${JSON.stringify(p)} is not a .md path`); continue; }
      const abs = safeRel(path.join(DOCS, dir), p, where);
      if (abs && !fs.existsSync(abs)) fail(`${where}: page ${p} does not exist`);
      if (pageSet.has(p)) fail(`${where}: page ${p} listed twice`);
      pageSet.add(p);
    }
    for (const f of walk(path.join(DOCS, dir), ".md")) {
      const rel = path.relative(path.join(DOCS, dir), f);
      if (!pageSet.has(rel)) fail(`${where}: page ${rel} is not listed in contribution.yml`);
    }

    const exports = Array.isArray(m.exports) ? m.exports : [];
    if (!exports.some((e) => e?.kind === "theorem")) fail(`${where}: needs at least one exported theorem`);
    for (const [i, e] of exports.entries()) {
      const at = `${where} exports[${i}]`;
      if (!e || typeof e !== "object") { fail(`${at}: not a mapping`); continue; }
      for (const k of Object.keys(e)) if (!EXPORT_KEYS.has(k)) fail(`${at}: unknown field ${k}`);
      if (!KINDS.has(e.kind)) fail(`${at}: kind must be theorem or definition`);
      if (typeof e.name !== "string" || !e.name.startsWith(ns + ".")) fail(`${at}: ${e.name} is not inside ${ns}`);
      if (!pageSet.has(e.page)) fail(`${at}: page ${e.page} is not one of this contribution's pages`);
      if (typeof e.label !== "string" || !LABEL_RE.test(e.label)) { fail(`${at}: bad label ${JSON.stringify(e.label)}`); continue; }
      if (!e.label.includes(m.id)) fail(`${at}: label ${e.label} should contain the contribution id ${m.id}`);
      if (seen.labels.has(e.label)) fail(`${at}: label ${e.label} also bound in ${seen.labels.get(e.label)}`);
      seen.labels.set(e.label, at);
      if (pageSet.has(e.page)) {
        const text = fs.readFileSync(path.join(DOCS, dir, e.page), "utf8");
        const n = [...text.matchAll(new RegExp(`^\\s*:label:\\s*${e.label}\\s*$|^\\(${e.label}\\)=\\s*$`, "gm"))].length;
        if (n !== 1) fail(`${at}: label ${e.label} appears ${n} times in ${e.page}, expected exactly once`);
      }
    }
    manifests.push({ ...m, dir, leanDir: comps[1], exports, pages });
  }
  // Every Lean contribution directory needs a manifest.
  if (fs.existsSync(path.join(LEAN, LIB))) {
    const claimed = new Set(manifests.map((m) => m.leanDir));
    for (const d of listDirs(path.join(LEAN, LIB)))
      if (!RESERVED_LEAN.has(d) && !claimed.has(d)) fail(`lean/${LIB}/${d}: no docs/<id>/contribution.yml claims it`);
  }
  return manifests;
}

// ------------------------------------------------------------------- snippets, umbrella

// Every literalinclude must point inside the repo at an existing file, and its
// start-after/end-before markers must each occur exactly once, in that order.
function checkSnippets(manifests) {
  const pages = [path.join(DOCS, "index.md"),
    ...manifests.flatMap((m) => m.pages.map((p) => path.join(DOCS, m.dir, p)))];
  const re = /```\{literalinclude\}\s+(\S+)\s*\n((?::[^\n]*\n)*)/g;
  for (const page of pages) {
    if (!fs.existsSync(page)) continue;
    const text = fs.readFileSync(page, "utf8");
    const at = path.relative(ROOT, page);
    for (const m of text.matchAll(re)) {
      const target = safeRel(path.dirname(page), m[1], at);
      if (!target) continue;
      if (!fs.existsSync(target)) { fail(`${at}: literalinclude ${m[1]} does not exist`); continue; }
      const src = fs.readFileSync(target, "utf8");
      const opt = (k) => (m[2].match(new RegExp(`^:${k}:\\s*(.*)$`, "m")) || [])[1]?.trim();
      const pos = {};
      for (const k of ["start-after", "end-before"]) {
        const marker = opt(k);
        if (!marker) continue;
        const count = src.split(marker).length - 1;
        if (count !== 1) fail(`${at}: marker "${marker}" occurs ${count} times in ${m[1]}`);
        pos[k] = src.indexOf(marker);
      }
      if (pos["start-after"] !== undefined && pos["end-before"] !== undefined && pos["start-after"] > pos["end-before"])
        fail(`${at}: markers in ${m[1]} are in the wrong order`);
    }
  }
}

function umbrellaText() {
  const mods = walk(path.join(LEAN, LIB), ".lean")
    .map((f) => path.relative(LEAN, f).replace(/\.lean$/, "").split(path.sep).join("."))
    .sort();
  return ["module", "",
    "-- Generated by `node tools/lemmata.mjs umbrella --write` -- do not edit.",
    `-- Imports every module under ${LIB}/, for downstream users. Contributions import the`,
    "-- specific modules they need instead, which keeps the import graph acyclic.",
    ...mods.map((m) => `public import ${m}`), ""].join("\n");
}

function checkUmbrella(write) {
  const file = path.join(LEAN, `${LIB}.lean`);
  const want = umbrellaText();
  if (write) { fs.writeFileSync(file, want); return; }
  const have = fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "";
  if (have !== want) fail(`lean/${LIB}.lean is out of date: run node tools/lemmata.mjs umbrella --write`);
}

// ------------------------------------------------------------------------- generation

function verifierRequest(manifests) {
  return {
    root: LIB,
    allowed_axioms: ALLOWED_AXIOMS,
    exports: manifests.flatMap((m) => m.exports.map((e) =>
      ({ contribution: m.id, name: e.name, kind: e.kind, namespace: m.lean_namespace }))),
  };
}

const esc = (s) => String(s).replace(/[<>&`]/g, (c) => ({ "<": "&lt;", ">": "&gt;", "&": "&amp;", "`": "\\`" }[c]));

function titleOf(m) {
  const text = fs.readFileSync(path.join(DOCS, m.dir, "index.md"), "utf8");
  const fm = text.match(/^---\n([\s\S]*?)\n---/);
  return (fm && YAML.parse(fm[1])?.title) || m.id;
}

// Panels and catalog come only from the verifier's report, never from page content.
function prepare(manifests, report, { commit, sourceUrl }) {
  const gen = path.join(DOCS, "_generated");
  fs.rmSync(gen, { recursive: true, force: true });
  fs.mkdirSync(path.join(gen, "verification"), { recursive: true });
  const passed = report?.result === "passed";
  const byName = new Map((report?.exports ?? []).map((e) => [e.name, e]));
  const link = (file) => sourceUrl && commit ? `${sourceUrl.replace(/\/$/, "")}/-/blob/${commit}/${file}` : null;

  const rows = [];
  for (const m of manifests) {
    const lines = [":::{card} Formal verification", ""];
    for (const e of m.exports) {
      const r = byName.get(e.name);
      const ok = passed && r?.status === "checked";
      const badge = !report ? "**○ not verified (preview)**"
        : ok ? (e.kind === "definition" ? "**◇ elaborated definition**" : "**✓ checked**")
        : "**✗ failed**";
      const src = r && link(r.source_file);
      const axioms = r?.axioms?.length ? r.axioms.map((a) => `\`${a}\``).join(", ") : "none";
      lines.push(`- ${badge} [](#${e.label}) — \`${e.name}\`` +
        (src ? ` ([source](${src}))` : "") + ` — axioms: ${axioms}`);
    }
    lines.push("",
      report ? `Checked by \`${esc(report.tool ?? "lemmata-check")}\` on Lean ${esc(report.lean_version ?? "?")}` +
        `${commit ? ` at commit \`${commit.slice(0, 12)}\`` : ""}, policy \`${POLICY_ID}\`` +
        ` (allowed axioms: ${ALLOWED_AXIOMS.map((a) => `\`${a}\``).join(", ")}).`
      : "This is a local preview: nothing on this page has been verified.",
      "The formal statement is machine-checked; that it matches the prose is checked by review.",
      ":::", "");
    fs.writeFileSync(path.join(gen, "verification", `${m.id}.md`), lines.join("\n"));
    rows.push(`| [${esc(titleOf(m))}](../${m.dir}/index.md) | ${m.exports.length} | ` +
      (!report ? "preview" : m.exports.every((e) => passed && byName.get(e.name)?.status === "checked") ? "checked" : "failed") + " |");
  }
  fs.writeFileSync(path.join(gen, "catalog.md"),
    ["## Entries", "", "| Entry | Formal results | Status |", "|---|---|---|", ...rows, ""].join("\n"));

  // Effective MyST config: the authored one plus the generated TOC. Parsed and re-emitted
  // as YAML, never patched as text. Kept next to myst.yml so relative paths mean the same.
  const cfg = YAML.parse(fs.readFileSync(path.join(DOCS, "myst.yml"), "utf8"));
  if (cfg.extends) fail("docs/myst.yml: `extends` is not allowed");
  if (cfg.project?.plugins) fail("docs/myst.yml: build plugins are not allowed");
  cfg.project.toc = [{ file: "index.md" },
    ...manifests.map((m) => m.pages.length === 1 ? { file: `${m.dir}/index.md` }
      : { file: `${m.dir}/index.md`, children: m.pages.slice(1).map((p) => ({ file: `${m.dir}/${p}` })) })];
  if (process.env.LEMMATA_THEME) cfg.site.template = process.env.LEMMATA_THEME;
  fs.writeFileSync(path.join(DOCS, "myst.runtime.yml"),
    "# Generated by tools/lemmata.mjs prepare -- do not edit, not committed.\n" + YAML.stringify(cfg));
}

function scaffold(id, lean) {
  if (!ID_RE.test(id) || RESERVED_DOCS.has(id)) { fail(`bad id ${id}`); return; }
  if (!LEAN_COMPONENT_RE.test(lean) || RESERVED_LEAN.has(lean)) { fail(`bad Lean name ${lean}`); return; }
  const d = path.join(DOCS, id), l = path.join(LEAN, LIB, lean);
  if (fs.existsSync(d) || fs.existsSync(l)) { fail(`docs/${id} or lean/${LIB}/${lean} already exists`); return; }
  fs.mkdirSync(d, { recursive: true }); fs.mkdirSync(l, { recursive: true });
  const thm = `${LIB}.${lean}.main`;
  fs.writeFileSync(path.join(d, "contribution.yml"), YAML.stringify({ schema_version: 1, id,
    lean_namespace: `${LIB}.${lean}`, pages: ["index.md"],
    exports: [{ name: thm, kind: "theorem", page: "index.md", label: `thm-${id}` }] }));
  fs.writeFileSync(path.join(d, "index.md"), `---\ntitle: ${id}\nauthors:\n  - name: Your Name\n---\n\n` +
    "```{prf:theorem} Statement\n:label: thm-" + id + "\n\nState the result here.\n```\n\n" +
    "```{literalinclude} ../../lean/" + LIB + "/" + lean + "/Main.lean\n:language: lean\n" +
    ":start-after: -- DOCS_BEGIN_MAIN\n:end-before: -- DOCS_END_MAIN\n```\n\n" +
    "```{include} ../_generated/verification/" + id + ".md\n```\n");
  fs.writeFileSync(path.join(l, "Main.lean"), `module\n\npublic import Mathlib.Logic.Function.Basic\n\npublic section\n\n` +
    `namespace ${LIB}.${lean}\n\n-- DOCS_BEGIN_MAIN\ntheorem main : True := trivial\n-- DOCS_END_MAIN\n\nend ${LIB}.${lean}\n`);
  checkUmbrella(true);
  console.log(`created docs/${id}/ and lean/${LIB}/${lean}/; umbrella updated`);
}

// ------------------------------------------------------------------------------- main

const [cmd, ...args] = process.argv.slice(2);
const flag = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
switch (cmd) {
  case "validate": {
    const ms = loadManifests(); checkSnippets(ms); checkUmbrella(false);
    if (fs.existsSync(path.join(ROOT, ".publication"))) fail(".publication/ must not be committed");
    finish(`ok: ${ms.length} contribution(s), ${ms.reduce((n, m) => n + m.exports.length, 0)} export(s)`);
    break;
  }
  case "umbrella": checkUmbrella(args.includes("--write")); finish(args.includes("--write") ? "umbrella written" : "umbrella up to date"); break;
  case "request": {
    const ms = loadManifests(); finish();
    fs.writeFileSync(args[0], JSON.stringify(verifierRequest(ms), null, 2) + "\n"); break;
  }
  case "prepare": {
    const ms = loadManifests(); finish();
    const report = args[0] && args[0] !== "--preview" ? JSON.parse(fs.readFileSync(args[0], "utf8")) : null;
    prepare(ms, report, { commit: flag("--commit"), sourceUrl: flag("--source-url") });
    finish("prepared docs/_generated and docs/myst.runtime.yml"); break;
  }
  case "new": scaffold(args[0], args[1]); finish(); break;
  default:
    console.error("usage: lemmata.mjs validate | umbrella [--write] | request <out> | prepare <report.json>|--preview [--commit SHA] [--source-url URL] | new <id> <LeanName>");
    process.exit(2);
}
