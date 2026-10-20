#!/usr/bin/env node
// Repository tooling for Lemmata. One file, no dependencies besides `yaml`, so the
// cluster's build Job can run the same code a contributor runs locally.
//
//   node tools/lemmata.mjs validate            structure, manifests, pairing, snippets, umbrella
//   node tools/lemmata.mjs umbrella [--write]  check (or regenerate) lean/Lemmata.lean
//   node tools/lemmata.mjs request <out.json>  verifier request built from the manifests
//   node tools/lemmata.mjs prepare <report.json> [--commit SHA] [--source-url URL]
//                                              generated pages + docs/myst.runtime.yml
//   node tools/lemmata.mjs new <id> <LeanName> <category>   scaffold a new contribution
//
// Exit status is non-zero on any problem; every problem is printed, not just the first.

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { execFileSync } from "node:child_process";
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
  "index", "healthz", "readyz", "node_modules", "c", "changelog", "abs", "llms"]);
// Category overview pages are generated at docs/c/<category>/index.md (URL /c/<category>/),
// under a reserved prefix so category ids and entry ids can never collide.
const CATEGORY_DIR = "c";
const CATEGORY_KEYS = new Set(["id", "title", "description"]);
const RESERVED_LEAN = new Set(["Shared"]);
const MANIFEST_KEYS = new Set(["schema_version", "id", "lean_namespace", "category", "tags", "arxiv", "contributors",
  "ai_use", "acknowledgements", "pages", "exports"]);
// Free-text notes rendered at the bottom of an entry. Inline MyST only: text, emphasis,
// links and math ($...$, $$...$$, rendered by KaTeX). Anything that could create page
// structure or pull in other content is refused, so a note cannot impersonate the
// verification panel or include files.
const NOTE_KEYS = { ai_use: "AI use", acknowledgements: "Acknowledgements" };
const NOTE_MAX_CHARS = 2000;
function checkNote(text, at) {
  if (typeof text !== "string" || !text.trim()) { fail(`${at}: must be non-empty text`); return null; }
  if (text.length > NOTE_MAX_CHARS) { fail(`${at}: longer than ${NOTE_MAX_CHARS} characters`); return null; }
  const bad = [[/^\s*(```|~~~|:::)/m, "code fences or directives"], [/\{[a-z][\w:-]*\}`/i, "roles such as {eval}`...`"],
    [/^\s*#/m, "headings"], [/^\s*\(.*\)=\s*$/m, "labels"], [/<\s*\/?\s*[a-z]/i, "HTML"], [/^\s*[-*+]\s|^\s*\d+\.\s/m, "lists"]];
  for (const [re, what] of bad) if (re.test(text)) { fail(`${at}: ${what} are not allowed (inline text, links and $math$ only)`); return null; }
  // Balanced $ / $$ so a stray dollar does not swallow the rest of the page into math.
  const dollars = (text.replace(/\\\$/g, "").match(/\$/g) ?? []).length;
  if (dollars % 2) { fail(`${at}: unbalanced $ (escape a literal dollar as \\$)`); return null; }
  return text.trim();
}
// arXiv identifiers: new style 2301.01234 (4 or 5 digits after the dot, since 2015), old
// style math/0601001 or math.AG/0601001; each optionally with a version vN.
const ARXIV_RE = /^(?:\d{4}\.\d{4,5}|[a-z-]+(?:\.[A-Z]{2})?\/\d{7})(?:v\d+)?$/;
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

function arxivIds(source) {
  const node = YAML.parseDocument(source).get("arxiv", true);
  if (node === undefined || node === null) return [];
  const items = YAML.isSeq(node) ? node.items : [node];
  return items.map((x) => (YAML.isScalar(x) ? (x.source ?? String(x.value)) : x)).map((v) => typeof v === "string" ? v.trim() : v);
}

// --------------------------------------------------------------------------- categories

// docs/categories.yml is the one list of allowed categories, in display order. Entries
// name one primary `category` (where they sit in the sidebar) and optional `tags`
// (further categories whose overview pages also list them). An unknown id is an error,
// so a typo cannot quietly create a new category.
function loadCategories() {
  const file = path.join(DOCS, "categories.yml");
  if (!fs.existsSync(file)) { fail("docs/categories.yml is missing"); return []; }
  let list;
  try { list = YAML.parse(fs.readFileSync(file, "utf8"), { uniqueKeys: true }); }
  catch (e) { fail(`docs/categories.yml: ${e.message}`); return []; }
  if (!Array.isArray(list) || !list.length) { fail("docs/categories.yml must be a non-empty list"); return []; }
  const seen = new Set();
  const out = [];
  for (const [i, c] of list.entries()) {
    const at = `docs/categories.yml[${i}]`;
    if (!c || typeof c !== "object") { fail(`${at}: not a mapping`); continue; }
    for (const k of Object.keys(c)) if (!CATEGORY_KEYS.has(k)) fail(`${at}: unknown field ${k}`);
    if (typeof c.id !== "string" || !ID_RE.test(c.id)) { fail(`${at}: id must be lowercase kebab-case`); continue; }
    if (seen.has(c.id)) fail(`${at}: duplicate id ${c.id}`);
    if (typeof c.title !== "string" || !c.title.trim()) fail(`${at}: title is required`);
    if (c.description !== undefined && typeof c.description !== "string") fail(`${at}: description must be text`);
    seen.add(c.id);
    out.push({ id: c.id, title: String(c.title ?? c.id), description: c.description ?? "" });
  }
  return out;
}

// ---------------------------------------------------------------------------- manifests

function loadManifests(categories = loadCategories()) {
  const catIds = new Set(categories.map((c) => c.id));
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
    if (!catIds.has(m.category))
      fail(`${where}/contribution.yml: category ${JSON.stringify(m.category)} is not in docs/categories.yml (${[...catIds].join(", ")})`);
    if (m.tags !== undefined && !Array.isArray(m.tags)) fail(`${where}/contribution.yml: tags must be a list`);
    for (const t of Array.isArray(m.tags) ? m.tags : []) {
      if (!catIds.has(t)) fail(`${where}/contribution.yml: tag ${JSON.stringify(t)} is not in docs/categories.yml`);
      if (t === m.category) fail(`${where}/contribution.yml: tag ${t} repeats the primary category`);
    }

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
    // The two generated panels are not optional: an entry must show who contributed it
    // (from git) and what was checked (from the verifier), and only the tools write them.
    if (pageSet.has("index.md")) {
      const idx = fs.readFileSync(path.join(DOCS, dir, "index.md"), "utf8");
      for (const [kind, what] of [["provenance", "contributors line"], ["verification", "verification panel"]]) {
        const inc = `{include} ../_generated/${kind}/${dir}.md`;
        if (idx.split(inc).length - 1 !== 1) fail(`${where}/index.md: must include the ${what} exactly once: \`\`\`${inc}\``);
      }
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
    // Optional arXiv id(s) for additional material; shown linked under the title. Read
    // from the YAML source text, not the parsed value: unquoted, 2301.10230 parses as the
    // number 2301.1023 -- a link to a different paper.
    const arxiv = arxivIds(fs.readFileSync(mfPath, "utf8"));
    for (const a of arxiv) {
      if (typeof a !== "string" || !ARXIV_RE.test(a))
        fail(`${where}/contribution.yml: arxiv ${JSON.stringify(a)} is not an arXiv identifier (e.g. 2301.01234, 2301.01234v2, math/0601001)`);
    }
    if (new Set(arxiv).size !== arxiv.length) fail(`${where}/contribution.yml: arxiv lists an identifier twice`);
    // Optional explicit contributors: replaces the git-derived names (git knows who
    // committed, not who wrote it). Each item is "First Last" or {first, last} -- the
    // mapping form is for surnames with several parts ("van Beethoven", "García Márquez").
    const contributors = [];
    if (m.contributors !== undefined) {
      if (!Array.isArray(m.contributors) || !m.contributors.length) fail(`${where}/contribution.yml: contributors must be a non-empty list`);
      for (const [i, c] of (Array.isArray(m.contributors) ? m.contributors : []).entries()) {
        const at = `${where}/contribution.yml: contributors[${i}]`;
        if (typeof c === "string") {
          const t = c.trim().replace(/\s+/g, " ");
          if (!t || /[{}\\@<>]/.test(t)) { fail(`${at}: ${JSON.stringify(c)} is not a plain name`); continue; }
          contributors.push({ name: t });
        } else if (c && typeof c === "object" && !Array.isArray(c)) {
          for (const k of Object.keys(c)) if (!["first", "last"].includes(k)) fail(`${at}: unknown field ${k} (use first, last)`);
          const first = String(c.first ?? "").trim(), last = String(c.last ?? "").trim();
          if (!last) { fail(`${at}: last is required`); continue; }
          if (/[{}\\@<>]/.test(first + last)) { fail(`${at}: names must be plain text`); continue; }
          contributors.push({ name: first ? `${first} ${last}` : last, first, last });
        } else fail(`${at}: must be a name or {first, last}`);
      }
      const seen = new Set();
      for (const c of contributors) { if (seen.has(c.name)) fail(`${where}/contribution.yml: contributor ${c.name} listed twice`); seen.add(c.name); }
    }
    const notes = {};
    for (const k of Object.keys(NOTE_KEYS)) if (m[k] !== undefined) notes[k] = checkNote(m[k], `${where}/contribution.yml: ${k}`);
    manifests.push({ ...m, dir, leanDir: comps[1], exports, pages, tags: Array.isArray(m.tags) ? m.tags : [], arxiv, contributors, notes });
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

// BibTeX for one entry. Every field comes from data the tools trust: title from the page,
// authors and year from git (provenance), ids from the manifest, URLs from the site.
// `url` is the STABLE address (/<id>/, which redirects to the current release); the
// immutable snapshot of this exact version goes in `note`, so a citation is both durable
// and exact. No `urldate`: it would be the build date, not the reader's.
const bibEscape = (v) => String(v).replace(/[\\{}]/g, "").replace(/([&%$#_])/g, "\\$1");
// Names stay exactly as git has them ("Ludwig van Beethoven"): BibTeX parses
// "First von Last" itself, particles included, which a naive reordering gets wrong.
const bibName = (n) => n.trim().replace(/\s+/g, " ");
// Who to credit: the manifest's explicit list if given, else everyone who committed.
const people = (m, p) => m.contributors.length ? m.contributors : (p?.contributors ?? []);
// A {first, last} name is written "{Last}, First": braces keep a multi-part surname whole.
const bibAuthor = (c) => c.last !== undefined
  ? (c.first ? `{${bibEscape(c.last)}}, ${bibEscape(c.first)}` : `{${bibEscape(c.last)}}`)
  : bibEscape(bibName(c.name));
function bibtex(m, title, p, { siteUrl, releaseUrl, commit, checked, ident }) {
  // With an identifier, both the key and the URL are the permanent ones; the directory
  // name is an internal detail that may change.
  const stable = ident ? `${siteUrl}/abs/${ident}` : `${siteUrl}/${m.dir}/`;
  const fields = [
    ["title", `{${bibEscape(title)}}`],
    ["author", people(m, p).length ? people(m, p).map(bibAuthor).join(" and ") : "{Lemmata contributors}"],
    ["howpublished", ident ? `Lemmata, lemmata:${ident}, \\url{${stable}}` : `Lemmata, \\url{${stable}}`],
    ["year", p ? p.first.date.slice(0, 4) : String(new Date().getUTCFullYear())],
    ["url", stable],
  ];
  const note = [commit ? `Version ${commit.slice(0, 12)}` : null, checked ? "formal statements checked in Lean 4" : null,
    releaseUrl ? `snapshot: \\url{${releaseUrl}/${m.dir}/}` : null].filter(Boolean).join("; ");
  fields.push(["note", note]);
  if (m.arxiv.length) fields.push(["eprint", m.arxiv[0]], ["archivePrefix", "arXiv"]);
  const key = ident ? `lemmata:${ident}` : `lemmata:${m.dir}`;
  const w = Math.max(...fields.map(([k]) => k.length));
  return `@misc{${key},\n` + fields.map(([k, v]) => `  ${k.padEnd(w)} = {${v.replace(/^\{(.*)\}$/s, "$1")}}`).join(",\n") + "\n}";
}

// .lemmata/provenance.json if the cluster supplied it; otherwise compute the same shape
// from local git (a working checkout), or null if there is no git at all.
// Stable identifiers (lemmata:YYYY.NNNNN) are assigned by the cluster and shipped as
// .lemmata/identifiers.json; a local preview has none ("assigned on publication").
function loadIdentifiers(commit) {
  const shipped = path.join(ROOT, ".lemmata", "identifiers.json");
  if (!fs.existsSync(shipped)) return {};
  const d = JSON.parse(fs.readFileSync(shipped, "utf8"));
  if (commit && d.source_commit && d.source_commit !== commit) fail(`.lemmata/identifiers.json is for ${d.source_commit}, not ${commit}`);
  for (const [entry, ident] of Object.entries(d.entries ?? {}))
    if (!/^\d{4}\.\d{5}$/.test(ident)) fail(`.lemmata/identifiers.json: bad identifier ${ident} for ${entry}`);
  return d.entries ?? {};
}

function loadProvenance(manifests, commit) {
  const shipped = path.join(ROOT, ".lemmata", "provenance.json");
  if (fs.existsSync(shipped)) {
    const p = JSON.parse(fs.readFileSync(shipped, "utf8"));
    if (commit && p.source_commit !== commit) fail(`.lemmata/provenance.json is for ${p.source_commit}, not ${commit}`);
    return p;
  }
  const git = (...a) => execFileSync("git", ["-C", ROOT, ...a], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] });
  try { git("rev-parse", "HEAD"); } catch { return null; }
  const out = { schema_version: 1, source_commit: git("rev-parse", "HEAD").trim(), entries: {} };
  for (const m of manifests) {
    const log = git("log", "--no-merges", "--format=%H%x1f%an%x1f%ae%x1f%aI", "HEAD", "--", `docs/${m.dir}`, `lean/${LIB}/${m.leanDir}`);
    const commits = log.split("\n").filter(Boolean).map((l) => { const [hash, name, email, date] = l.split("\x1f"); return { hash, name, email: email.toLowerCase(), date }; });
    if (!commits.length) continue;
    const people = new Map();
    for (const c of [...commits].reverse()) {
      const p = people.get(c.email) ?? { name: c.name, commits: 0, first: c.date };
      p.commits++; p.name = c.name; people.set(c.email, p);
    }
    out.entries[m.id] = {
      contributors: [...people.values()].sort((a, b) => b.commits - a.commits || a.first.localeCompare(b.first)).map(({ name, commits }) => ({ name, commits })),
      first: { commit: commits.at(-1).hash, date: commits.at(-1).date },
      last: { commit: commits[0].hash, date: commits[0].date },
    };
  }
  return out;
}

// Panels and catalog come only from the verifier's report, never from page content.
// Links into the content repository, for whichever forge hosts it. The repository's web
// address is the only required input (the build Job gets it as SOURCE_WEB_URL, from the
// cluster's one CONTENT_WEB setting), so moving the repo is a configuration change.
// GitLab puts "/-/" before blob/commit; GitHub, Gitea and Forgejo do not. The style is
// guessed from the host name ("gitlab" in it), and SOURCE_FORGE=gitlab|github overrides
// the guess -- needed for self-hosted GitLab under another name, such as git.zib.de.
function forgeLinks(webUrl, forge = process.env.SOURCE_FORGE) {
  if (!webUrl) return null;
  const base = webUrl.replace(/\/+$/, "").replace(/\.git$/, "");
  const gitlab = forge ? forge === "gitlab" : /gitlab/i.test(new URL(base).host);
  const sep = gitlab ? "/-" : "";
  return { blob: (sha, file) => `${base}${sep}/blob/${sha}/${file}`, commit: (sha) => `${base}${sep}/commit/${sha}` };
}

function prepare(manifests, categories, report, { commit, sourceUrl }) {
  const forge = forgeLinks(sourceUrl);
  const gen = path.join(DOCS, "_generated");
  const catRoot = path.join(DOCS, CATEGORY_DIR);
  for (const d of [gen, catRoot]) fs.rmSync(d, { recursive: true, force: true });
  fs.mkdirSync(path.join(gen, "verification"), { recursive: true });
  const passed = report?.result === "passed";
  const byName = new Map((report?.exports ?? []).map((e) => [e.name, e]));
  const link = (file) => forge && commit ? forge.blob(commit, file) : null;
  const statusOf = (m) => !report ? "preview"
    : m.exports.every((e) => passed && byName.get(e.name)?.status === "checked") ? "checked" : "failed";

  // Verification panel per entry, from the verifier's report only.
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
    // AI use statement and acknowledgements close the entry, after the verification panel.
    const notes = Object.entries(NOTE_KEYS).filter(([k]) => m.notes?.[k]);
    if (notes.length) {
      lines.push(":::{div}", ":class: lemmata-notes", "");
      for (const [k, title] of notes) lines.push(`**${title}.** ${m.notes[k]}`, "");
      lines.push(":::", "");
    }
    fs.writeFileSync(path.join(gen, "verification", `${m.id}.md`), lines.join("\n"));
  }

  // Contributors line per entry. In the cluster the controller computes it from git and
  // ships .lemmata/provenance.json with the source (the build sees no history); locally the
  // same is computed from this checkout's git log. Names only -- never email addresses.
  // Public address of the site, and of this build's immutable release. In the cluster the
  // build Job sets both (SITE_URL, and BASE_URL = /_releases/<id>); locally they default to
  // the production site and no snapshot link.
  const siteUrl = (process.env.SITE_URL ?? "https://lemmata.iol.berlin").replace(/\/$/, "");
  const releaseUrl = process.env.BASE_URL?.startsWith("/_releases/") ? siteUrl + process.env.BASE_URL : null;
  const prov = loadProvenance(manifests, commit);
  const idents = loadIdentifiers(commit);
  fs.mkdirSync(path.join(gen, "provenance"), { recursive: true });
  const day = (iso) => String(iso ?? "").slice(0, 10);
  const commitLink = (c) => forge ? `[${c.slice(0, 7)}](${forge.commit(c)})` : `\`${c.slice(0, 7)}\``;
  for (const m of manifests) {
    const p = prov?.entries?.[m.id];
    // One header block per entry: contributors line + "Cite as", visually set apart from
    // the mathematics below (styled by docs/_static/lemmata.css, class lemmata-header).
    const ident = idents[m.id];
    const lines = [":::::{div}", ":class: lemmata-header", "", ":::{div}", ":class: lemmata-provenance", ""];
    // The stable identifier and its permanent URL, the address to cite and link to.
    lines.push(ident ? `[**lemmata:${ident}**](${siteUrl}/abs/${ident})  ` : "*Identifier assigned on publication.*  ");
    if (!p && !m.contributors.length) lines.push("*Not yet committed.*");
    else if (!p) lines.push(`Contributed by ${people(m, p).map((c) => `**${esc(c.name)}**`).join(", ")}`);
    else {
      lines.push(`Contributed by ${people(m, p).map((c) => `**${esc(c.name)}**`).join(", ")}  `);
      lines.push(p.first.commit === p.last.commit
        ? `Published ${day(p.first.date)} (${commitLink(p.first.commit)})`
        : day(p.first.date) === day(p.last.date)
          ? `Published ${day(p.first.date)} · last changed in ${commitLink(p.last.commit)}`
          : `First published ${day(p.first.date)} · last changed ${day(p.last.date)} (${commitLink(p.last.commit)})`);
    }
    if (m.arxiv.length) {
      if (lines.at(-1) !== "" && !lines.at(-1).endsWith("  ")) lines[lines.length - 1] += "  ";
      lines.push(`Additional material: ${m.arxiv.map((a) => `[arXiv:${a}](https://arxiv.org/abs/${a})`).join(", ")}`);
    }
    lines.push(":::", "");
    // "Cite as": a collapsed dropdown with a bibtex block (MyST adds the copy button).
    lines.push("::::{dropdown} Cite as", "", "```bibtex",
      bibtex(m, titleOf(m), p, { siteUrl, releaseUrl, commit, checked: statusOf(m) === "checked", ident }), "```", "::::", "",
      ":::::", "");
    fs.writeFileSync(path.join(gen, "provenance", `${m.id}.md`), lines.join("\n"));
  }

  // Entries per category: primary members (sidebar + catalog) and tagged members (also
  // listed on the category page), each sorted by title.
  const byTitle = (a, b) => titleOf(a).localeCompare(titleOf(b));
  const primary = new Map(categories.map((c) => [c.id, manifests.filter((m) => m.category === c.id).sort(byTitle)]));
  const tagged = new Map(categories.map((c) => [c.id, manifests.filter((m) => m.tags.includes(c.id)).sort(byTitle)]));
  const used = categories.filter((c) => primary.get(c.id).length || tagged.get(c.id).length);
  // `rel` is the path prefix from the page that will contain the table to docs/: links in
  // generated text must be relative to the page MyST renders them on (an included file
  // resolves against the INCLUDING page; `../<id>/index.md` from _generated/ once
  // rendered as a raw href and 404'd).
  const table = (list, rel) => ["| Entry | Formal results | Status |", "|---|---|---|",
    ...list.map((m) => `| [${esc(titleOf(m))}](${rel}${m.dir}/index.md) | ${m.exports.length} | ${statusOf(m)} |`)];

  // Landing page catalog (included from docs/index.md, so rel = "").
  const cat = ["## Entries", ""];
  for (const c of used) {
    if (!primary.get(c.id).length) continue;
    cat.push(`### [${esc(c.title)}](${CATEGORY_DIR}/${c.id}/index.md)`, "");
    if (c.description) cat.push(esc(c.description), "");
    cat.push(...table(primary.get(c.id), ""), "");
  }
  fs.writeFileSync(path.join(gen, "catalog.md"), cat.join("\n"));

  // One overview page per category at /c/<id>/ (a real page, so the URL is stable and
  // the sidebar group header is clickable). Written into the build tree only.
  for (const c of used) {
    const dir = path.join(catRoot, c.id);
    fs.mkdirSync(dir, { recursive: true });
    const lines = ["---", `title: ${JSON.stringify(c.title)}`, "---", ""];
    if (c.description) lines.push(esc(c.description), "");
    if (primary.get(c.id).length) lines.push(...table(primary.get(c.id), "../../"), "");
    if (tagged.get(c.id).length) {
      lines.push("## Also related", "", ...table(tagged.get(c.id), "../../"), "");
    }
    fs.writeFileSync(path.join(dir, "index.md"), lines.join("\n"));
  }

  // Effective MyST config: the authored one plus the generated TOC. Parsed and re-emitted
  // as YAML, never patched as text. Kept next to myst.yml so relative paths mean the same.
  // The sidebar groups entries under their category page; entry URLs come from their own
  // directories (/<id>/), so moving an entry to another category never breaks a link.
  const cfg = YAML.parse(fs.readFileSync(path.join(DOCS, "myst.yml"), "utf8"));
  if (cfg.extends) fail("docs/myst.yml: `extends` is not allowed");
  if (cfg.project?.plugins) fail("docs/myst.yml: build plugins are not allowed");
  const entryToc = (m) => m.pages.length === 1 ? { file: `${m.dir}/index.md` }
    : { file: `${m.dir}/index.md`, children: m.pages.slice(1).map((p) => ({ file: `${m.dir}/${p}` })) };
  cfg.project.toc = [{ file: "index.md" },
    ...used.filter((c) => primary.get(c.id).length).map((c) => ({
      file: `${CATEGORY_DIR}/${c.id}/index.md`,
      children: primary.get(c.id).map(entryToc),
    })),
    // The maintained changelog, a hand-written page (docs/changelog.md), last in the sidebar.
    ...(fs.existsSync(path.join(DOCS, "changelog.md")) ? [{ file: "changelog.md" }] : [])];
  if (process.env.LEMMATA_THEME) cfg.site.template = process.env.LEMMATA_THEME;
  fs.writeFileSync(path.join(DOCS, "myst.runtime.yml"),
    "# Generated by tools/lemmata.mjs prepare -- do not edit, not committed.\n" + YAML.stringify(cfg));
}

function scaffold(id, lean, category) {
  if (!ID_RE.test(id) || RESERVED_DOCS.has(id)) { fail(`bad id ${id}`); return; }
  if (!LEAN_COMPONENT_RE.test(lean) || RESERVED_LEAN.has(lean)) { fail(`bad Lean name ${lean}`); return; }
  const cats = loadCategories().map((c) => c.id);
  if (!cats.includes(category)) { fail(`category ${JSON.stringify(category)} is not in docs/categories.yml (${cats.join(", ")})`); return; }
  const d = path.join(DOCS, id), l = path.join(LEAN, LIB, lean);
  if (fs.existsSync(d) || fs.existsSync(l)) { fail(`docs/${id} or lean/${LIB}/${lean} already exists`); return; }
  fs.mkdirSync(d, { recursive: true }); fs.mkdirSync(l, { recursive: true });
  const thm = `${LIB}.${lean}.main`;
  fs.writeFileSync(path.join(d, "contribution.yml"), YAML.stringify({ schema_version: 1, id,
    lean_namespace: `${LIB}.${lean}`, category, pages: ["index.md"],
    exports: [{ name: thm, kind: "theorem", page: "index.md", label: `thm-${id}` }] }));
  // No `authors:` block: who contributed is shown from git, under the title.
  fs.writeFileSync(path.join(d, "index.md"), `---\ntitle: ${id}\n---\n\n` +
    "```{include} ../_generated/provenance/" + id + ".md\n```\n\n" +
    "```{prf:theorem} Statement\n:label: thm-" + id + "\n\nState the result here.\n```\n\n" +
    "```{literalinclude} ../../lean/" + LIB + "/" + lean + "/Main.lean\n:language: lean\n" +
    ":start-after: -- DOCS_BEGIN_MAIN\n:end-before: -- DOCS_END_MAIN\n```\n\n" +
    "```{include} ../_generated/verification/" + id + ".md\n```\n");
  fs.writeFileSync(path.join(l, "Main.lean"), `module\n\npublic import Mathlib.Logic.Function.Basic\n\npublic section\n\n` +
    `namespace ${LIB}.${lean}\n\n-- DOCS_BEGIN_MAIN\ntheorem main : True := trivial\n-- DOCS_END_MAIN\n\nend ${LIB}.${lean}\n`);
  checkUmbrella(true);
  console.log(`created docs/${id}/ and lean/${LIB}/${lean}/; umbrella updated`);
}

// ------------------------------------------------------------------------- site index

// Machine-readable views of the archive, written into the rendered site after `myst
// build`: llms.txt (the llms.txt convention: Markdown, one line per entry), lemmata.json
// (everything an agent needs to cite or link a result), and a sitemap.xml/robots.txt with
// the public addresses -- MyST's own pointed at its internal build server
// (http://localhost:3000). Entries are listed by their permanent /abs/ URL when they
// have an identifier, so links into the index never depend on directory names.
function siteIndex(manifests, categories, report, outDir, { commit, sourceUrl }) {
  const siteUrl = (process.env.SITE_URL ?? "https://lemmata.iol.berlin").replace(/\/$/, "");
  const prov = loadProvenance(manifests, commit), idents = loadIdentifiers(commit);
  const passed = report?.result === "passed";
  const byName = new Map((report?.exports ?? []).map((e) => [e.name, e]));
  const catTitle = new Map(categories.map((c) => [c.id, c.title]));
  const entries = manifests.map((m) => {
    const ident = idents[m.id] ?? null, p = prov?.entries?.[m.id];
    const url = ident ? `${siteUrl}/abs/${ident}` : `${siteUrl}/${m.dir}/`;
    const exports = m.exports.map((e) => { const r = byName.get(e.name);
      return { name: e.name, kind: e.kind, label: e.label, status: passed && r?.status === "checked" ? "checked" : "failed",
               axioms: r?.axioms ?? [], source_file: r?.source_file ?? null }; });
    return {
      identifier: ident ? `lemmata:${ident}` : null, url, title: titleOf(m),
      category: m.category, category_title: catTitle.get(m.category) ?? m.category, tags: m.tags,
      contributors: people(m, p).map((c) => c.name),
      first_published: p?.first.date ?? null, last_changed: p?.last.date ?? null,
      status: exports.every((x) => x.status === "checked") ? "checked" : "failed",
      exports, arxiv: m.arxiv, ai_use: m.notes?.ai_use ?? null, acknowledgements: m.notes?.acknowledgements ?? null,
      bibtex: bibtex(m, titleOf(m), p, { siteUrl, releaseUrl: null, commit, checked: exports.every((x) => x.status === "checked"), ident }),
    };
  }).sort((a, b) => (a.identifier ?? "~").localeCompare(b.identifier ?? "~") || a.title.localeCompare(b.title));

  fs.writeFileSync(path.join(outDir, "lemmata.json"), JSON.stringify({
    schema_version: 1, site: siteUrl, source_commit: commit ?? null,
    checked_means: `formal statements compile, are accepted by Lean's kernel, and use no axioms beyond ${ALLOWED_AXIOMS.join(", ")}; the correspondence between prose and Lean statement is checked by human review`,
    entries,
  }, null, 2) + "\n");

  const line = (e) => `- [${e.title}](${e.url})${e.identifier ? ` (${e.identifier})` : ""}: ${e.status}` +
    `${e.contributors.length ? `; ${e.contributors.join(", ")}` : ""}${e.arxiv.length ? `; arXiv:${e.arxiv.join(", arXiv:")}` : ""}`;
  const md = ["# Lemmata", "",
    "> An experimental mathematics repository: each entry is a result written as prose and formalized in Lean 4 on Mathlib. " +
    "\"checked\" means the formal statements compile, are accepted by Lean's kernel, and use no axioms beyond " +
    `${ALLOWED_AXIOMS.join(", ")}. Whether the prose and the Lean statement say the same thing is checked by human review.`, "",
    `Cite an entry by its identifier and permanent URL (${siteUrl}/abs/YYYY.NNNNN). Machine-readable index with exported Lean ` +
    `declarations, axioms and BibTeX: ${siteUrl}/lemmata.json`, ""];
  for (const c of categories) {
    const list = entries.filter((e) => e.category === c.id);
    if (list.length) md.push(`## ${c.title}`, "", ...list.map(line), "");
  }
  md.push("## Optional", "", `- [Changelog](${siteUrl}/changelog/)`, `- [Build status](${siteUrl}/_status)`, "");
  fs.writeFileSync(path.join(outDir, "llms.txt"), md.join("\n"));

  const xmlEsc = (u) => u.replace(/&/g, "&amp;").replace(/</g, "&lt;");
  const urls = [`${siteUrl}/`, ...categories.filter((c) => entries.some((e) => e.category === c.id)).map((c) => `${siteUrl}/c/${c.id}/`),
    ...entries.map((e) => e.url), `${siteUrl}/changelog/`];
  fs.writeFileSync(path.join(outDir, "sitemap.xml"), ['<?xml version="1.0" encoding="UTF-8"?>',
    '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
    ...urls.map((u) => `  <url><loc>${xmlEsc(u)}</loc></url>`), "</urlset>", ""].join("\n"));
  // No Disallow for /_releases/: the stable and /abs/ URLs redirect there, so blocking it
  // would hide every page from crawlers that honour robots.txt.
  fs.writeFileSync(path.join(outDir, "robots.txt"), ["User-agent: *", "Allow: /",
    `Sitemap: ${siteUrl}/sitemap.xml`, ""].join("\n"));
}

// ------------------------------------------------------------------------------- main

const [cmd, ...args] = process.argv.slice(2);
const flag = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
switch (cmd) {
  case "validate": {
    const ms = loadManifests(); checkSnippets(ms); checkUmbrella(false);
    if (fs.existsSync(path.join(ROOT, ".publication"))) fail(".publication/ must not be committed");
    // .lemmata/ is where the cluster puts data it adds to the source (provenance.json).
    // Locally it must not exist; in a build (LEMMATA_BUILD=1) it is expected, and the
    // controller has already refused any commit that contained it.
    if (!process.env.LEMMATA_BUILD && fs.existsSync(path.join(ROOT, ".lemmata")))
      fail(".lemmata/ is reserved for data the cluster adds; it must not be committed");
    finish(`ok: ${ms.length} contribution(s), ${ms.reduce((n, m) => n + m.exports.length, 0)} export(s)`);
    break;
  }
  case "umbrella": checkUmbrella(args.includes("--write")); finish(args.includes("--write") ? "umbrella written" : "umbrella up to date"); break;
  case "request": {
    const ms = loadManifests(); finish();
    fs.writeFileSync(args[0], JSON.stringify(verifierRequest(ms), null, 2) + "\n"); break;
  }
  case "prepare": {
    const cats = loadCategories(); const ms = loadManifests(cats); finish();
    const report = args[0] && args[0] !== "--preview" ? JSON.parse(fs.readFileSync(args[0], "utf8")) : null;
    prepare(ms, cats, report, { commit: flag("--commit"), sourceUrl: flag("--source-url") });
    finish("prepared docs/_generated and docs/myst.runtime.yml"); break;
  }
  case "new": scaffold(args[0], args[1], args[2]); finish(); break;
  case "site-index": {            // after myst build: llms.txt, lemmata.json, sitemap, robots
    const cats = loadCategories(); const ms = loadManifests(cats); finish();
    const report = args[0] ? JSON.parse(fs.readFileSync(args[0], "utf8")) : null;
    siteIndex(ms, cats, report, args[1], { commit: flag("--commit"), sourceUrl: flag("--source-url") });
    finish(`wrote llms.txt, lemmata.json, sitemap.xml, robots.txt to ${args[1]}`); break;
  }
  case "provenance": {            // what the controller ships for HEAD, from local git
    const ms = loadManifests(); finish();
    process.stdout.write(JSON.stringify(loadProvenance(ms, null), null, 2) + "\n"); break;
  }
  default:
    console.error("usage: lemmata.mjs validate | umbrella [--write] | request <out> | prepare <report.json>|--preview [--commit SHA] [--source-url URL] | new <id> <LeanName> <category>");
    process.exit(2);
}
