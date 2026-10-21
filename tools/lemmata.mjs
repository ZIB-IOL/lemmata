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
  "index", "healthz", "readyz", "node_modules", "c", "a", "changelog", "abs", "html", "llms", "checked", "about"]);
// The page that explains what "checked" means (docs/checked.md), linked from every
// verification panel; entries are at docs/<id>/, so the link is one level up.
const CHECKED_PAGE_LINK = "../checked.md";
// Category overview pages are generated at docs/c/<category>/index.md (URL /c/<category>/),
// under a reserved prefix so category ids and entry ids can never collide.
const CATEGORY_DIR = "c";
// Author pages at /a/<slug>/: every entry a person is credited on, like arXiv's author
// search. Keyed by the displayed name (git author name, or the manifest's contributors);
// names only, never emails. Not an identity: two people with one name share a page.
const AUTHOR_DIR = "a";
// The collapsible "Cite as" box with the BibTeX under the header. Replaced by a copy button
// next to the identifier (2026-10-21); kept so it can be switched back on.
const SHOW_CITE_BOX = false;
// Comments under each entry with Giscus (GitHub Discussions). Off until a PUBLIC repository
// with Discussions and the Giscus app exists: fill in its ids (from giscus.app) to enable.
const GISCUS = null;   // e.g. { repo: "ZIB-IOL/lemmata-discussions", repoId: "R_...", category: "Comments", categoryId: "DIC_..." }
const CATEGORY_KEYS = new Set(["id", "title", "description"]);
const RESERVED_LEAN = new Set(["Shared"]);
const MANIFEST_KEYS = new Set(["schema_version", "id", "lean_namespace", "category", "tags", "arxiv", "contributors",
  "ai_use", "acknowledgements", "abstract", "license", "withdrawn", "related", "pages", "exports"]);
// Optional derived material attached to an entry: slides, videos, a monograph, code, ...
// Each is {kind, title, url}; shown as a list at the end of the entry.
const RELATED_KINDS = new Set(["slides", "video", "paper", "book", "notes", "code", "talk", "other"]);
// Licence of an entry (prose and Lean). Optional; without it the entry is CC BY 4.0. Only
// these SPDX ids are accepted, so every entry stays reusable and its link is known.
const LICENSES = {
  "CC-BY-4.0": { name: "CC BY 4.0", url: "https://creativecommons.org/licenses/by/4.0/" },
  "CC-BY-SA-4.0": { name: "CC BY-SA 4.0", url: "https://creativecommons.org/licenses/by-sa/4.0/" },
  "CC0-1.0": { name: "CC0 1.0", url: "https://creativecommons.org/publicdomain/zero/1.0/" },
};
const DEFAULT_LICENSE = "CC-BY-4.0";
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
      else checkProofs(fs.readFileSync(f, "utf8"), `${where}/${rel}`);
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
    // Optional abstract for the entry's /abs/ page; inline only, like the notes.
    if (m.abstract === undefined) fail(`${where}/contribution.yml: abstract is required (one paragraph, inline text and $math$)`);
    else notes.abstract = checkNote(m.abstract, `${where}/contribution.yml: abstract`);
    // Withdrawn: the reason, shown as a notice on the entry and its /abs/ page. A withdrawn
    // entry is never deleted (identifiers are cited, other entries may import its Lean):
    // it is still built and checked, only left out of the sidebar and the listings.
    if (m.withdrawn !== undefined) notes.withdrawn = checkNote(m.withdrawn, `${where}/contribution.yml: withdrawn`);
    if (m.license !== undefined && !Object.hasOwn(LICENSES, m.license))
      fail(`${where}/contribution.yml: license must be one of ${Object.keys(LICENSES).join(", ")} (default ${DEFAULT_LICENSE})`);
    const license = Object.hasOwn(LICENSES, m.license) ? m.license : DEFAULT_LICENSE;
    const related = [];
    if (m.related !== undefined) {
      if (!Array.isArray(m.related)) fail(`${where}/contribution.yml: related must be a list of {kind, title, url}`);
      for (const [i, r] of (Array.isArray(m.related) ? m.related : []).entries()) {
        const at = `${where}/contribution.yml: related[${i}]`;
        if (!r || typeof r !== "object") { fail(`${at}: must be {kind, title, url}`); continue; }
        for (const k of Object.keys(r)) if (!["kind", "title", "url"].includes(k)) fail(`${at}: unknown field ${k}`);
        if (!RELATED_KINDS.has(r.kind)) fail(`${at}: kind must be one of ${[...RELATED_KINDS].join(", ")}`);
        let u = null; try { u = new URL(r.url); } catch {}
        if (!u || !["https:", "http:"].includes(u.protocol) || /["'<>\s]/.test(r.url)) fail(`${at}: url must be a plain http(s) URL`);
        const title = typeof r.title === "string" ? checkNote(r.title, `${at}: title`) : (fail(`${at}: title is required`), null);
        if (title && u) related.push({ kind: r.kind, title, url: r.url });
      }
    }
    manifests.push({ ...m, dir, leanDir: comps[1], exports, pages, tags: Array.isArray(m.tags) ? m.tags : [], arxiv, contributors, notes, license, related });
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
// MyST numbers proofs like theorems, so an entry with a theorem, a proposition and one
// proof shows "Proof 1" and leaves the reader guessing what it proves. Every proof is
// therefore unnumbered and names its statement with a link:
//   ```{prf:proof} of [](#thm-<id>)
//   :nonumber:
// which renders as "Proof (of Theorem 1)". No project-wide switch does this: MyST's
// numbering config ignores proofs.
function checkProofs(text, where) {
  const lines = text.split("\n");
  for (const [i, line] of lines.entries()) {
    const m = line.match(/^\s*(`{3,}|:{3,})\{prf:proof\}(.*)$/);
    if (!m) continue;
    const at = `${where}:${i + 1}`;
    if (!/\]\(#[^)\s]+\)/.test(m[2])) fail(`${at}: a proof must say what it proves, e.g. \`${m[1]}{prf:proof} of [](#thm-…)\``);
    let nonumber = false;
    for (let j = i + 1; j < lines.length && /^\s*:[\w-]+:/.test(lines[j]); j++)
      if (/^\s*:nonumber:/.test(lines[j])) nonumber = true;
    if (!nonumber) fail(`${at}: a proof must be unnumbered: add \`:nonumber:\` on the line after the directive`);
  }
}

// DOI links. MyST treats every doi.org link (and doi:…) as a citation and looks it up
// online while rendering, unless docs/references.bib already has an entry with that DOI.
// The cluster renders offline -- the render step shares its pod, and so its network
// policy, with the untrusted Lean build -- so an unresolved DOI fails only there
// ("Could not find DOI"), long after a local check passed. Hence: every DOI linked from
// docs/ must be in references.bib, and `lemmata.mjs doi` fetches the missing entries on
// the contributor's (online) machine.
const BIB = path.join(DOCS, "references.bib");
const DOI_LINK_RE = /(?:https?:\/\/(?:dx\.|www\.)?doi\.org\/|\bdoi:)(10\.\d{4,9}\/[^\s)>\]"'`]+)/gi;
const doiNorm = (d) => decodeURIComponent(d).replace(/[.,;:]+$/, "").toLowerCase();
// The hand-written pages: the start page, checked/changelog, and every entry's pages.
function linkedDois(manifests) {
  const out = new Map();     // normalised DOI -> first place it is linked
  const pages = ["index.md", "checked.md", "changelog.md", "about.md"].map((p) => path.join(DOCS, p))
    .concat(manifests.flatMap((m) => m.pages.map((p) => path.join(DOCS, m.dir, p))));
  for (const f of pages) {
    if (!fs.existsSync(f)) continue;
    const rel = path.relative(ROOT, f);
    fs.readFileSync(f, "utf8").split("\n").forEach((line, i) => {
      for (const m of line.matchAll(DOI_LINK_RE)) { const d = doiNorm(m[1]); if (!out.has(d)) out.set(d, `${rel}:${i + 1}`); }
    });
  }
  return out;
}
const bibDois = () => new Set([...(fs.existsSync(BIB) ? fs.readFileSync(BIB, "utf8") : "")
  .matchAll(/(?:^|[\s,{])doi\s*=\s*[{"]\s*([^}"]+?)\s*[}"]/gim)].map((m) => doiNorm(m[1])));
function checkDois(manifests) {
  const have = bibDois();
  for (const [d, at] of linkedDois(manifests))
    if (!have.has(d)) fail(`${at}: DOI ${d} is not in docs/references.bib (the cluster renders offline); run: node tools/lemmata.mjs doi`);
}
// `doi`: append a BibTeX entry from doi.org for every linked DOI that references.bib lacks.
async function fetchDois(manifests) {
  const have = bibDois(), missing = [...linkedDois(manifests).keys()].filter((d) => !have.has(d));
  if (!missing.length) { console.log("references.bib already has every linked DOI"); return; }
  let bib = fs.existsSync(BIB) ? fs.readFileSync(BIB, "utf8") : "";
  for (const d of missing) {
    const r = await fetch(`https://doi.org/${d}`, { headers: { accept: "application/x-bibtex; charset=utf-8" } });
    const text = (await r.text()).trim();
    if (!r.ok || !text.startsWith("@")) { fail(`DOI ${d}: doi.org answered ${r.status}; check the DOI, or add its entry to docs/references.bib by hand`); continue; }
    // doi.org's own keys (Padberg_1982) can collide; make them unique and readable.
    let key = text.match(/^@\w+\{([^,]+),/)?.[1] ?? "ref", k = key, n = 1;
    while (new RegExp(`\\{${k.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`).test(bib)) k = `${key}_${++n}`;
    bib = bib.replace(/\s*$/, "\n\n") + text.replace(/^(@\w+\{)[^,]+,/, `$1${k},`).replace(/\s+\n/g, "\n") + "\n";
    console.log(`added ${d} as ${k}`);
  }
  fs.writeFileSync(BIB, bib);
}

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
  const frozen = loadFrozen();          // not built, so not checked: they keep their last result
  return {
    root: LIB,
    allowed_axioms: ALLOWED_AXIOMS,
    exports: manifests.filter((m) => !frozen[m.id]).flatMap((m) => m.exports.map((e) =>
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
// `url` is the permanent identifier URL (/abs/YYYY.NNNNN, or /<dir>/ before one is
// assigned); the commit in `note` names the exact version. No `urldate`: it would be the
// build date, not the reader's.
const bibEscape = (v) => String(v).replace(/[\\{}]/g, "").replace(/([&%$#_])/g, "\\$1");
// Names stay exactly as git has them ("Ludwig van Beethoven"): BibTeX parses
// "First von Last" itself, particles included, which a naive reordering gets wrong.
const bibName = (n) => n.trim().replace(/\s+/g, " ");
// Who to credit: the manifest's explicit list if given, else everyone who committed.
// The withdrawal notice, first thing on the entry and on its /abs/ page.
const withdrawnNotice = (m) => m.notes?.withdrawn
  ? [":::{div}", ":class: lemmata-withdrawn", "", `**Withdrawn.** ${m.notes.withdrawn}`, "",
     "The entry stays available under its identifier as a record; it is no longer listed as a current entry.", ":::", ""]
  : [];
const licenseLine = (m) => `License: [${LICENSES[m.license].name}](${LICENSES[m.license].url})`;
const people = (m, p) => m.contributors.length ? m.contributors : (p?.contributors ?? []);
const authorSlug = (name) => name.normalize("NFKD").replace(/[\u0300-\u036f]/g, "").toLowerCase()
  .replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "") || "unknown";
// A {first, last} name is written "{Last}, First": braces keep a multi-part surname whole.
const bibAuthor = (c) => c.last !== undefined
  ? (c.first ? `{${bibEscape(c.last)}}, ${bibEscape(c.first)}` : `{${bibEscape(c.last)}}`)
  : bibEscape(bibName(c.name));
function bibtex(m, title, p, { siteUrl, commit, checked, ident }) {
  // With an identifier, both the key and the URL are the permanent ones; the directory
  // name is an internal detail that may change.
  const stable = ident ? `${siteUrl}/abs/${ident}` : `${siteUrl}/${m.dir}/`;
  const fields = [
    ["title", `{${bibEscape(title)}}`],
    ["author", people(m, p).length ? people(m, p).map(bibAuthor).join(" and ") : "{Lemmata Repository contributors}"],
    ["howpublished", ident ? `Lemmata Repository, lemmata:${ident}, \\url{${stable}}` : `Lemmata Repository, \\url{${stable}}`],
    ["year", p ? p.first.date.slice(0, 4) : String(new Date().getUTCFullYear())],
    ["url", stable],
  ];
  // No snapshot URL: old releases are pruned, so a citation must not depend on one. The
  // permanent /abs/ URL always resolves; the commit names the exact version cited.
  const note = [commit ? `Version ${commit.slice(0, 12)}` : null, checked ? "formal statements checked in Lean 4" : null]
    .filter(Boolean).join("; ");
  if (note) fields.push(["note", note]);
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

// Entries an admin froze, with their last successful check (commit, versions, date,
// results), shipped by the cluster as .lemmata/frozen.json. Empty outside the cluster.
function loadFrozen() {
  const f = path.join(ROOT, ".lemmata", "frozen.json");
  return fs.existsSync(f) ? (JSON.parse(fs.readFileSync(f, "utf8")).entries ?? {}) : {};
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
  const absRoot = path.join(DOCS, "abs");
  const authorRoot = path.join(DOCS, AUTHOR_DIR);
  for (const d of [gen, catRoot, absRoot, authorRoot]) fs.rmSync(d, { recursive: true, force: true });
  fs.mkdirSync(path.join(gen, "verification"), { recursive: true });
  const passed = report?.result === "passed";
  const byName = new Map((report?.exports ?? []).map((e) => [e.name, e]));
  const link = (file) => forge && commit ? forge.blob(commit, file) : null;
  // Frozen entries (admin decision, see lemmata-code/frozen.json) were not built: they keep
  // their last successful check, shown with its Lean version and date.
  const frozen = loadFrozen();
  const statusOf = (m) => frozen[m.id] ? "frozen" : !report ? "preview"
    : m.exports.every((e) => passed && byName.get(e.name)?.status === "checked") ? "checked" : "failed";

  // Verification panel per entry, from the verifier's report only.
  for (const m of manifests) {
    // Collapsed, with the outcome in the bar: one click opens the per-result list.
    const fz = frozen[m.id], n = m.exports.length;
    const okCount = fz ? m.exports.filter((e) => (fz.results ?? []).some((x) => x.name === e.name && x.status === "checked")).length
      : m.exports.filter((e) => passed && byName.get(e.name)?.status === "checked").length;
    const summary = !report && !fz ? `○ not verified (local preview)`
      : okCount === n ? `✅ ${n === 1 ? "the formal result is" : `all ${n} formal results are`} ${fz ? "checked" : "kernel-checked"}`
      : `✗ ${n - okCount} of ${n} formal results not checked`;
    const lines = [`::::{dropdown} Formal verification — ${summary}`, ":class: lemmata-verification", ""];
    if (fz) {
      const old = new Map((fz.results ?? []).map((x) => [x.name, x]));
      for (const e of m.exports) {
        const ok = old.get(e.name)?.status === "checked";
        const badge = ok ? (e.kind === "definition" ? "**◇ elaborated definition**" : "**✓ kernel-checked**") : "**✗ not checked**";
        const src = forge ? forge.blob(fz.commit, `lean/${LIB}/${m.leanDir}`) : null;
        lines.push(`- ${badge} [](#${e.label}) — \`${e.name}\`` + (src ? ` ([source](${src}))` : ""));
      }
      lines.push("", `**Last checked with Lean v${esc(fz.lean_version ?? "?")} on ${String(fz.checked_at ?? "").slice(0, 10)}** ` +
        `(commit \`${String(fz.commit).slice(0, 12)}\`)` +
        (report?.lean_version && report.lean_version !== fz.lean_version ? `; not re-checked with the current Lean v${esc(report.lean_version)}.` : ".") +
        " The Lean source shown is unchanged since that check. " +
        `[What "checked" means](${CHECKED_PAGE_LINK}).`, "::::", "");
    }
    else for (const e of m.exports) {
      const r = byName.get(e.name);
      const ok = passed && r?.status === "checked";
      const lean = report?.lean_version ? ` (Lean v${esc(report.lean_version)})` : "";
      const badge = !report ? "**○ not verified (preview)**"
        : ok ? (e.kind === "definition" ? `**◇ elaborated definition${lean}**` : `**✓ kernel-checked${lean}**`)
        : "**✗ failed**";
      const src = r && link(r.source_file);
      // The axioms a result uses are not listed here: every published result is held to
      // the same policy (see the "checked" page), and lemmata.json carries them per result.
      lines.push(`- ${badge} [](#${e.label}) — \`${e.name}\`` + (src ? ` ([source](${src}))` : ""));
    }
    if (!fz) lines.push("",
      report ? `Checked${commit ? ` at commit \`${commit.slice(0, 12)}\`` : ""}. The formal statement is ` +
        "machine-checked; that it matches the prose is checked by review. " +
        `[What "checked" means](${CHECKED_PAGE_LINK}).`
      : "This is a local preview: nothing on this page has been verified.",
      "::::", "");
    // Related material, AI use, acknowledgements and the license close the entry.
    const notes = Object.entries(NOTE_KEYS).filter(([k]) => m.notes?.[k]);
    lines.push(":::{div}", ":class: lemmata-notes", "");
    if (m.related.length) {
      lines.push("**Related material.**", "");
      for (const r of m.related) lines.push(`- ${r.kind[0].toUpperCase() + r.kind.slice(1)}: [${r.title}](${r.url})`);
      lines.push("");
    }
    for (const [k, title] of notes) lines.push(`**${title}.** ${m.notes[k]}`, "");
    lines.push(licenseLine(m), "", ":::", "");
    // Comments, one discussion per entry (keyed by its directory, stable across renames of
    // the title). Only when GISCUS is configured.
    if (GISCUS) lines.push("```{raw} html",
      `<script src="https://giscus.app/client.js" data-repo="${GISCUS.repo}" data-repo-id="${GISCUS.repoId}" ` +
      `data-category="${GISCUS.category}" data-category-id="${GISCUS.categoryId}" data-mapping="specific" ` +
      `data-term="${m.id}" data-reactions-enabled="1" data-emit-metadata="0" data-input-position="top" ` +
      `data-theme="preferred_color_scheme" data-lang="en" data-loading="lazy" crossorigin="anonymous" async></script>`, "```", "");
    fs.writeFileSync(path.join(gen, "verification", `${m.id}.md`), lines.join("\n"));
  }

  // Contributors line per entry. In the cluster the controller computes it from git and
  // ships .lemmata/provenance.json with the source (the build sees no history); locally the
  // same is computed from this checkout's git log. Names only -- never email addresses.
  // Public address of the site (SITE_URL, set by the build Job; locally the production site).
  const siteUrl = (process.env.SITE_URL ?? "https://lemmata.iol.berlin").replace(/\/$/, "");
  const prov = loadProvenance(manifests, commit);
  const idents = loadIdentifiers(commit);
  fs.mkdirSync(path.join(gen, "provenance"), { recursive: true });
  // The identifier line's "copy" control: a tiny anywidget module written by the tools,
  // not taken from the content repo, so contributors cannot change what it does.
  fs.writeFileSync(path.join(gen, "provenance", "ident.mjs"), IDENT_WIDGET);
  const day = (iso) => String(iso ?? "").slice(0, 10);
  for (const m of manifests) {
    const p = prov?.entries?.[m.id];
    // One header block per entry, visually set apart from the mathematics below (styled by
    // docs/_static/lemmata.css, class lemmata-header): identifier with copy controls, the
    // authors (linked to their author pages), versions, and the abstract.
    const ident = idents[m.id];
    const bib = bibtex(m, titleOf(m), p, { siteUrl, commit, checked: statusOf(m) === "checked", ident });
    const lines = [...withdrawnNotice(m), ":::::{div}", ":class: lemmata-header", "", ":::{div}", ":class: lemmata-provenance", ""];
    // The stable identifier and its permanent URL, the address to cite and link to.
    if (ident) {
      // Identifier as permanent link, "copy URL" and "copy BibTeX", rendered by a widget.
      // Without JavaScript the identifier is still the page's /abs/ address.
      lines.push(":::",
        // Path relative to the entry page that includes this file (docs/<id>/index.md):
        // MyST resolves widget modules from the including page, not from _generated/.
        "", "```{anywidget} ../_generated/provenance/ident.mjs",
        JSON.stringify({ ident: `lemmata:${ident}`, url: `${siteUrl}/abs/${ident}`, bibtex: bib }), "```",
        "", ":::{div}", ":class: lemmata-provenance", "");
    } else lines.push("*Identifier assigned on publication.*  ");
    const who = people(m, p).map((c) => `[**${esc(c.name)}**](../${AUTHOR_DIR}/${authorSlug(c.name)}/index.md)`).join(", ");
    if (!p && !m.contributors.length) lines.push("*Not yet committed.*");
    else lines.push(who + (p ? "  " : ""));
    // Versions, arXiv style: "v1 <first> · last <date linked to the commit>".
    if (p) {
      const last = forge ? `[${day(p.last.date)}](${forge.commit(p.last.commit)})` : day(p.last.date);
      lines.push(p.first.commit === p.last.commit ? `v1 ${day(p.first.date)}` : `v1 ${day(p.first.date)} · last ${last}`);
    }
    if (m.arxiv.length) {
      if (lines.at(-1) !== "" && !lines.at(-1).endsWith("  ")) lines[lines.length - 1] += "  ";
      lines.push(`Additional material: ${m.arxiv.map((a) => `[arXiv:${a}](https://arxiv.org/abs/${a})`).join(", ")}`);
    }
    lines.push(":::", "");
    // "Cite as": the BibTeX in a collapsed box. Hidden since the copy button replaced it.
    if (SHOW_CITE_BOX) lines.push("::::{dropdown} Cite as", "", "```bibtex", bib, "```", "::::", "");
    if (m.notes?.abstract) lines.push(":::{div}", ":class: lemmata-abstract", "", `**Abstract.** ${m.notes.abstract}`, ":::", "");
    lines.push(":::::", "");
    fs.writeFileSync(path.join(gen, "provenance", `${m.id}.md`), lines.join("\n"));
  }

  // Entries per category: primary members (sidebar + catalog) and tagged members (also
  // listed on the category page), each sorted by title.
  const byTitle = (a, b) => titleOf(a).localeCompare(titleOf(b));
  // Withdrawn entries are not listed (they keep their pages and identifiers).
  const current = manifests.filter((m) => !m.notes?.withdrawn);
  const primary = new Map(categories.map((c) => [c.id, current.filter((m) => m.category === c.id).sort(byTitle)]));
  const tagged = new Map(categories.map((c) => [c.id, current.filter((m) => m.tags.includes(c.id)).sort(byTitle)]));
  const used = categories.filter((c) => primary.get(c.id).length || tagged.get(c.id).length);
  // `rel` is the path prefix from the page that will contain the table to docs/: links in
  // generated text must be relative to the page MyST renders them on (an included file
  // resolves against the INCLUDING page; `../<id>/index.md` from _generated/ once
  // rendered as a raw href and 404'd).
  const table = (list, rel) => ["| Entry | Formal results | Status |", "|---|---|---|",
    ...list.map((m) => `| [${esc(titleOf(m))}](${rel}${m.dir}/index.md) | ${m.exports.length} | ` +
      (statusOf(m) === "frozen" ? `checked with v${esc(frozen[m.id].lean_version ?? "?")}` : statusOf(m)) + " |")];

  // "Contributing" paragraph of the landing page, with the repository address from the
  // build (SOURCE_WEB_URL) rather than written into docs/index.md, so moving the
  // repository needs no content change.
  const repo = sourceUrl?.replace(/\/+$/, "").replace(/\.git$/, "");
  const repoFile = (f) => forge?.blob("main", f) ?? null;
  const repoLabel = repo ? repo.replace(/^https?:\/\//, "") : null;
  const contributing = (repo
    ? `The archive is a Git repository, [${repoLabel}](${repo}). New entries and changes ` +
      `arrive by pull request; the [contribution guide](${repoFile("CONTRIBUTING.md")}) (and ` +
      `[AGENTS.md](${repoFile("AGENTS.md")}), the same procedure written for coding agents) explains every step. `
    : "New entries and changes arrive by pull request against the archive's Git repository. ") +
    `The site rebuilds itself from \`main\` within minutes; the [build status](${siteUrl}/_status) shows which ` +
    "version is live and, for a commit that was not published, why.\n";
  // With a bold label for the start page; without, for a page that has its own heading (About).
  fs.writeFileSync(path.join(gen, "contributing.md"), "**Contributing.** " + contributing);
  fs.writeFileSync(path.join(gen, "contributing-body.md"), contributing);

  // Landing page catalog (included from docs/index.md, so rel = "").
  const cat = ["## Entries", ""];
  for (const c of used) {
    if (!primary.get(c.id).length) continue;
    cat.push(`### [${esc(c.title)}](${CATEGORY_DIR}/${c.id}/index.md)`, "");
    if (c.description) cat.push(esc(c.description), "");
    cat.push(...table(primary.get(c.id), ""), "");
  }
  fs.writeFileSync(path.join(gen, "catalog.md"), cat.join("\n"));

  // One landing page per entry with an identifier, at /abs/<ident>/ (like arXiv's abstract
  // page): title, identifier with copy, contributors, dates, abstract, status, Cite as and
  // a link to the full entry at /html/<ident>. Built here so it is part of each release.
  const absPages = [];
  for (const m of manifests) {
    const ident = idents[m.id];
    if (!ident) continue;
    // Directory "2610-00001": MyST turns dots in a page path into hyphens, so the page is
    // built at abs/2610-00001/ whatever we name it. The public URL keeps the identifier's
    // dot (/abs/2610.00001); the supervisor maps one to the other.
    const p = prov?.entries?.[m.id], dir = path.join(absRoot, ident.replace(".", "-"));
    fs.mkdirSync(dir, { recursive: true });
    const status = statusOf(m), lean = report?.lean_version ? ` with Lean v${esc(report.lean_version)}` : "";
    // Header in the same style as the entry's, built here rather than included: the copy
    // widget's module path is relative to the page, and this page sits one level deeper
    // (docs/abs/<ident>/index.md) than an entry (docs/<id>/index.md).
    const who = people(m, p).map((c) => `[**${esc(c.name)}**](../../${AUTHOR_DIR}/${authorSlug(c.name)}/index.md)`).join(", ");
    const last = p && (forge ? `[${day(p.last.date)}](${forge.commit(p.last.commit)})` : day(p.last.date));
    const dates = p ? (p.first.commit === p.last.commit ? `v1 ${day(p.first.date)}` : `v1 ${day(p.first.date)} · last ${last}`) : "";
    const bib = bibtex(m, titleOf(m), p, { siteUrl, commit, checked: statusOf(m) === "checked", ident });
    const L = ["---", "numbering:", "  headings: false", `title: ${JSON.stringify(titleOf(m))}`, "---", "", ...withdrawnNotice(m),
      ":::::{div}", ":class: lemmata-header", "",
      "```{anywidget} ../../_generated/provenance/ident.mjs",
      JSON.stringify({ ident: `lemmata:${ident}`, url: `${siteUrl}/abs/${ident}`, bibtex: bib }), "```", "",
      ":::{div}", ":class: lemmata-provenance", "",
      ...(who ? [`${who}  `] : []), ...(dates ? [`${dates}  `] : []), licenseLine(m), ":::", "",
      ...(SHOW_CITE_BOX ? ["::::{dropdown} Cite as", "", "```bibtex", bib, "```", "::::", ""] : []),
      ":::::", "",
      // Not "## Abstract": MyST lifts a section of that name above everything else on the
      // page. A bold label keeps the abstract below the header block, as on arXiv.
      "**Abstract.** " + m.notes.abstract, "",
      "## Status", "",
      status === "frozen" ? `**Last checked with Lean v${esc(frozen[m.id].lean_version ?? "?")} on ${String(frozen[m.id].checked_at ?? "").slice(0, 10)}**` +
        `${report?.lean_version && report.lean_version !== frozen[m.id].lean_version ? `; not re-checked with the current Lean v${esc(report.lean_version)}` : ""}. [What "checked" means](../../checked.md).`
      : status === "checked" ? `All formal results are **kernel-checked**${lean}. [What "checked" means](../../checked.md).`
        : status === "preview" ? "Not verified (local preview)." : "**Verification failed.**", "",
      // Relative (two levels up, to the entry's directory) so it reads as an internal link.
      `**[View the full entry →](../../${m.dir}/index.md)** · category: [${esc(categories.find((c) => c.id === m.category)?.title ?? m.category)}](../../${CATEGORY_DIR}/${m.category}/index.md)` +
        (m.arxiv.length ? ` · ${m.arxiv.map((a) => `[arXiv:${a}](https://arxiv.org/abs/${a})`).join(", ")}` : ""), ""];
    fs.writeFileSync(path.join(dir, "index.md"), L.join("\n"));
    absPages.push(`abs/${ident.replace(".", "-")}/index.md`);
  }

  // One overview page per category at /c/<id>/ (a real page, so the URL is stable and
  // the sidebar group header is clickable). Written into the build tree only.
  for (const c of used) {
    const dir = path.join(catRoot, c.id);
    fs.mkdirSync(dir, { recursive: true });
    const lines = ["---", "numbering:", "  headings: false", `title: ${JSON.stringify(c.title)}`, "---", ""];
    if (c.description) lines.push(esc(c.description), "");
    if (primary.get(c.id).length) lines.push(...table(primary.get(c.id), "../../"), "");
    if (tagged.get(c.id).length) {
      lines.push("## Also related", "", ...table(tagged.get(c.id), "../../"), "");
    }
    fs.writeFileSync(path.join(dir, "index.md"), lines.join("\n"));
  }

  // One page per author at /a/<slug>/, listing every entry they are credited on (current
  // ones first, withdrawn ones after), and an index of all authors at /a/. Written into the
  // build tree only, like the category pages; hidden from the sidebar.
  const byAuthor = new Map();          // slug -> {name, entries}
  for (const m of manifests) for (const c of people(m, prov?.entries?.[m.id])) {
    const k = authorSlug(c.name);
    if (!byAuthor.has(k)) byAuthor.set(k, { name: c.name, entries: [] });
    byAuthor.get(k).entries.push(m);
  }
  const authorPages = [];
  for (const [slug, a] of [...byAuthor].sort((x, y) => x[1].name.localeCompare(y[1].name))) {
    const dir = path.join(authorRoot, slug);
    fs.mkdirSync(dir, { recursive: true });
    const cur = a.entries.filter((m) => !m.notes?.withdrawn).sort(byTitle), gone = a.entries.filter((m) => m.notes?.withdrawn).sort(byTitle);
    const lines = ["---", "numbering:", "  headings: false", `title: ${JSON.stringify(a.name)}`, "---", "",
      `Entries in the Lemmata Repository credited to ${esc(a.name)}.`, ""];
    if (cur.length) lines.push(...table(cur, "../../"), "");
    if (gone.length) lines.push("## Withdrawn", "", ...table(gone, "../../"), "");
    fs.writeFileSync(path.join(dir, "index.md"), lines.join("\n"));
    authorPages.push(`${AUTHOR_DIR}/${slug}/index.md`);
  }
  if (byAuthor.size) {
    fs.writeFileSync(path.join(authorRoot, "index.md"), ["---", "numbering:", "  headings: false", "title: Authors", "---", "",
      ...[...byAuthor].sort((x, y) => x[1].name.localeCompare(y[1].name))
        .map(([slug, a]) => `- [${esc(a.name)}](${slug}/index.md) (${a.entries.length})`), ""].join("\n"));
    authorPages.unshift(`${AUTHOR_DIR}/index.md`);
  }

  // Effective MyST config: the authored one plus the generated TOC. Parsed and re-emitted
  // as YAML, never patched as text. Kept next to myst.yml so relative paths mean the same.
  // The sidebar groups entries under their category page; entry URLs come from their own
  // directories (/<id>/), so moving an entry to another category never breaks a link.
  const cfg = YAML.parse(fs.readFileSync(path.join(DOCS, "myst.yml"), "utf8"));
  if (cfg.extends) fail("docs/myst.yml: `extends` is not allowed");
  if (cfg.project?.plugins) fail("docs/myst.yml: build plugins are not allowed");
  // The sidebar shows only the site's own pages: a list of every entry and category would
  // grow without bound (2026-10-21). Entries are reached from the start page's catalog and
  // the category pages. They stay in the toc as ordinary pages under their category --
  // MyST does not number theorems or sections on `hidden` pages (measured) -- and the
  // sidebar hides them with CSS (.lemmata-toc-* in lemmata.css).
  const entryToc = (m) => m.pages.length === 1 ? { file: `${m.dir}/index.md` }
    : { file: `${m.dir}/index.md`, children: m.pages.slice(1).map((p) => ({ file: `${m.dir}/${p}` })) };
  cfg.project.toc = [{ file: "index.md" },
    ...used.filter((c) => primary.get(c.id).length).map((c) => ({
      file: `${CATEGORY_DIR}/${c.id}/index.md`,
      children: primary.get(c.id).map(entryToc),
    })),
    // Hand-written site pages, after the entries: what "checked" means, the changelog, and
    // the About page (who runs the site, who supports it), last in the sidebar.
    ...(fs.existsSync(path.join(DOCS, "checked.md")) ? [{ file: "checked.md" }] : []),
    ...(fs.existsSync(path.join(DOCS, "changelog.md")) ? [{ file: "changelog.md" }] : []),
    ...(fs.existsSync(path.join(DOCS, "about.md")) ? [{ file: "about.md" }] : []),
    // Withdrawn entries and the landing pages: built, not listed. (Hidden pages are not
    // numbered; a withdrawn entry keeps its content but loses theorem numbers, accepted.)
    ...manifests.filter((m) => m.notes?.withdrawn).flatMap((m) => m.pages.map((p) => ({ file: `${m.dir}/${p}`, hidden: true }))),
    ...absPages.map((f) => ({ file: f, hidden: true })),
    ...authorPages.map((f) => ({ file: f, hidden: true }))];
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
    "```{prf:proof} of [](#thm-" + id + ")\n:nonumber:\n\nProve it here.\n```\n\n" +
    "```{literalinclude} ../../lean/" + LIB + "/" + lean + "/Main.lean\n:language: lean\n" +
    ":start-after: -- DOCS_BEGIN_MAIN\n:end-before: -- DOCS_END_MAIN\n```\n\n" +
    "```{include} ../_generated/verification/" + id + ".md\n```\n");
  fs.writeFileSync(path.join(l, "Main.lean"), `module\n\npublic import Mathlib.Logic.Function.Basic\n\npublic section\n\n` +
    `namespace ${LIB}.${lean}\n\n-- DOCS_BEGIN_MAIN\ntheorem main : True := trivial\n-- DOCS_END_MAIN\n\nend ${LIB}.${lean}\n`);
  checkUmbrella(true);
  console.log(`created docs/${id}/ and lean/${LIB}/${lean}/; umbrella updated`);
}

// The identifier line as a widget: the permanent link, and "copy" which puts the permanent
// URL on the clipboard (feedback "copied" for 1.5 s). Only model.get is used -- the static
// MyST theme has no kernel.
const IDENT_WIDGET = `const COPY = '<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="currentColor" aria-hidden="true" width="18" height="18"><path stroke-linecap="round" stroke-linejoin="round" d="M15.75 17.25v3.375c0 .621-.504 1.125-1.125 1.125h-9.75a1.125 1.125 0 0 1-1.125-1.125V7.875c0-.621.504-1.125 1.125-1.125H6.75a9.06 9.06 0 0 1 1.5.124m7.5 10.376h3.375c.621 0 1.125-.504 1.125-1.125V11.25c0-4.46-3.243-8.161-7.5-8.876a9.06 9.06 0 0 0-1.5-.124H9.375c-.621 0-1.125.504-1.125 1.125v3.5m7.5 10.375H9.375a1.125 1.125 0 0 1-1.125-1.125v-9.25m12 6.625v-1.875a3.375 3.375 0 0 0-3.375-3.375h-1.5a1.125 1.125 0 0 1-1.125-1.125v-1.5a3.375 3.375 0 0 0-3.375-3.375H9.75"/></svg>';
const DONE = '<svg xmlns="http://www.w3.org/2000/svg" fill="none" viewBox="0 0 24 24" stroke-width="1.5" stroke="currentColor" aria-hidden="true" width="18" height="18"><path stroke-linecap="round" stroke-linejoin="round" d="m4.5 12.75 6 6 9-13.5"/></svg>';
// A copy control: same icon as on code blocks, check mark after copying. Text label optional.
function copyButton(text, what, label) {
  const btn = document.createElement("button"); btn.type = "button"; btn.className = "lemmata-ident-copy";
  const show = (icon) => { btn.innerHTML = icon + (label ? "<span>" + label + "</span>" : ""); };
  show(COPY); btn.title = "Copy " + what; btn.setAttribute("aria-label", "Copy " + what);
  btn.addEventListener("click", async () => {
    try { await navigator.clipboard.writeText(text); }
    catch { const t = document.createElement("textarea"); t.value = text; document.body.append(t); t.select(); document.execCommand("copy"); t.remove(); }
    show(DONE); btn.setAttribute("aria-label", "Copied"); setTimeout(() => { show(COPY); btn.setAttribute("aria-label", "Copy " + what); }, 1500);
  });
  return btn;
}
function render({ model, el }) {
  const ident = model.get("ident"), url = model.get("url"), bib = model.get("bibtex");
  const box = document.createElement("span"); box.className = "lemmata-ident";
  const a = document.createElement("a"); a.href = url; a.className = "lemmata-ident-link";
  const b = document.createElement("strong"); b.textContent = ident; a.append(b);
  const btn = copyButton(url, "the permanent URL " + url, "URL");
  // "Cite": copies the entry's BibTeX, the same text as in the (hidden) Cite-as box.
  const cite = bib ? copyButton(bib, "the BibTeX entry", "BibTeX") : null;
  const css = document.createElement("style");
  css.textContent = ".lemmata-ident{display:inline-flex;align-items:center;gap:.3rem;font-size:.875rem}" +
    ".lemmata-ident-link{color:inherit}" +
    ".lemmata-ident-copy{display:inline-flex;align-items:center;padding:0;border:0;background:transparent;cursor:pointer;" +
    "color:var(--myst-color-link-underline,currentColor);opacity:.8}" +
    ".lemmata-ident-copy:hover{opacity:1;color:var(--myst-color-link-hover,currentColor)}" +
    ".lemmata-ident-copy span{margin-left:.2rem;font-size:.8rem}";
  box.append(a, btn); if (cite) box.append(cite); el.append(css, box);
}
export default { render };
`;

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
  // Frozen entries are not in this build's report (they were not built); they keep the
  // results of their last check, exactly as the rendered pages show them.
  const frozen = loadFrozen();
  const entries = manifests.map((m) => {
    const ident = idents[m.id] ?? null, p = prov?.entries?.[m.id], fz = frozen[m.id];
    const url = ident ? `${siteUrl}/abs/${ident}` : `${siteUrl}/${m.dir}/`;
    const old = new Map((fz?.results ?? []).map((x) => [x.name, x]));
    const exports = m.exports.map((e) => { const r = byName.get(e.name);
      const ok = fz ? old.get(e.name)?.status === "checked" : passed && r?.status === "checked";
      return { name: e.name, kind: e.kind, label: e.label, status: ok ? "checked" : "failed",
               axioms: r?.axioms ?? [], source_file: r?.source_file ?? null }; });
    const allOk = exports.every((x) => x.status === "checked");
    return {
      identifier: ident ? `lemmata:${ident}` : null, url, html_url: ident ? `${siteUrl}/html/${ident}` : `${siteUrl}/${m.dir}/`,
      title: titleOf(m),
      category: m.category, category_title: catTitle.get(m.category) ?? m.category, tags: m.tags,
      contributors: people(m, p).map((c) => c.name),
      first_published: p?.first.date ?? null, last_changed: p?.last.date ?? null,
      // "withdrawn" says how the entry is listed; its formal results keep their own status.
      status: m.notes?.withdrawn ? "withdrawn" : fz ? (allOk ? "frozen" : "failed") : allOk ? "checked" : "failed",
      withdrawn: m.notes?.withdrawn ?? null,
      last_checked: fz ? { lean_version: fz.lean_version ?? null, checked_at: fz.checked_at ?? null, commit: fz.commit ?? null } : null,
      exports, arxiv: m.arxiv, license: m.license, license_url: LICENSES[m.license].url, ai_use: m.notes?.ai_use ?? null, acknowledgements: m.notes?.acknowledgements ?? null,
      bibtex: bibtex(m, titleOf(m), p, { siteUrl, commit, checked: !fz && allOk, ident }),
    };
  }).sort((a, b) => (a.identifier ?? "~").localeCompare(b.identifier ?? "~") || a.title.localeCompare(b.title));

  fs.writeFileSync(path.join(outDir, "lemmata.json"), JSON.stringify({
    schema_version: 1, site: siteUrl, source_commit: commit ?? null,
    checked_means: `formal statements compile, are accepted by Lean's kernel, and use no axioms beyond ${ALLOWED_AXIOMS.join(", ")}; the correspondence between prose and Lean statement is checked by human review`,
    entries,
  }, null, 2) + "\n");

  const line = (e) => `- [${e.title}](${e.url})${e.identifier ? ` (${e.identifier})` : ""}: ` +
    (e.status === "frozen" ? `last checked with Lean v${e.last_checked.lean_version ?? "?"} on ${String(e.last_checked.checked_at ?? "").slice(0, 10)}` : e.status) +
    `${e.contributors.length ? `; ${e.contributors.join(", ")}` : ""}${e.arxiv.length ? `; arXiv:${e.arxiv.join(", arXiv:")}` : ""}`;
  const md = ["# Lemmata Repository", "",
    "> An experimental mathematics repository: each entry is a result written as prose and formalized in Lean 4 on Mathlib. " +
    "\"kernel-checked\" means the formal statements compile and were accepted by Lean's kernel using only the standard " +
    `axioms (${siteUrl}/checked/). Whether the prose and the Lean statement say the same thing is checked by human review.`, "",
    `Each entry has an identifier lemmata:YYMM.NNNNN, a landing page ${siteUrl}/abs/YYMM.NNNNN (abstract, status, BibTeX) ` +
    `and the full entry at ${siteUrl}/html/YYMM.NNNNN. Cite the /abs/ URL. Machine-readable index with exported Lean ` +
    `declarations, axioms, licence and BibTeX: ${siteUrl}/lemmata.json. Entries are licensed CC BY 4.0 unless the ` +
    "entry says otherwise (CC BY-SA 4.0 or CC0 1.0).", ""];
  for (const c of categories) {
    const list = entries.filter((e) => e.category === c.id && e.status !== "withdrawn");
    if (list.length) md.push(`## ${c.title}`, "", ...list.map(line), "");
  }
  // Withdrawn entries stay reachable under their identifiers, so they are still indexed.
  const gone = entries.filter((e) => e.status === "withdrawn");
  if (gone.length) md.push("## Withdrawn", "", ...gone.map((e) => `- [${e.title}](${e.url})${e.identifier ? ` (${e.identifier})` : ""}: withdrawn`), "");
  // How to contribute, for agents reading this file. The repository address is the build's
  // SOURCE_WEB_URL (the cluster's one CONTENT_WEB setting), never written in here, so a
  // moved repository is reflected on the next build.
  const repo = sourceUrl?.replace(/\/+$/, "").replace(/\.git$/, "");
  if (repo) {
    const file = (f) => forgeLinks(repo)?.blob("main", f) ?? `${repo}/${f}`;
    md.push("## Contributing", "",
      `New entries and corrections are pull requests against \`main\` of ${repo}. An agent should follow ` +
      `AGENTS.md there: it is the complete procedure (scaffold, Lean and prose rules, local checks with ` +
      `tools/check.sh, the pull request, and how to confirm publication via ${siteUrl}/_status.json).`, "",
      `- [AGENTS.md](${file("AGENTS.md")}): step-by-step procedure for agents`,
      `- [CONTRIBUTING.md](${file("CONTRIBUTING.md")}): the same for people`,
      `- [Repository](${repo})`, "");
  }
  md.push("## Optional", "", `- [What "kernel-checked" means](${siteUrl}/checked/)`, `- [Changelog](${siteUrl}/changelog/)`, `- [About](${siteUrl}/about/)`,
    `- [Build status](${siteUrl}/_status)`, "");
  fs.writeFileSync(path.join(outDir, "llms.txt"), md.join("\n"));

  const xmlEsc = (u) => u.replace(/&/g, "&amp;").replace(/</g, "&lt;");
  const urls = [`${siteUrl}/`, ...categories.filter((c) => entries.some((e) => e.category === c.id)).map((c) => `${siteUrl}/c/${c.id}/`),
    ...entries.map((e) => e.url), ...entries.filter((e) => e.identifier).map((e) => e.url.replace("/abs/", "/html/")),
    `${siteUrl}/checked/`, `${siteUrl}/changelog/`, `${siteUrl}/about/`];
  fs.writeFileSync(path.join(outDir, "sitemap.xml"), ['<?xml version="1.0" encoding="UTF-8"?>',
    '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
    ...urls.map((u) => `  <url><loc>${xmlEsc(u)}</loc></url>`), "</urlset>", ""].join("\n"));
  // Pages built for the site root are served at their stable URLs; /_releases/<id>/ are
  // copies for debugging that go stale, so keep crawlers off them. A release built with
  // the prefix lives only there, so it is left crawlable.
  fs.writeFileSync(path.join(outDir, "robots.txt"), ["User-agent: *", "Allow: /",
    ...(process.env.BASE_URL ? [] : ["Disallow: /_releases/"]),
    `Sitemap: ${siteUrl}/sitemap.xml`, ""].join("\n"));
  dedupeTitles(outDir);
  injectEnhancements(outDir);
}

// The theme titles every page "<page title> - <site title>". On the start page both are
// the site title, so tabs and link previews (Slack, og:title) read "X - X". Collapse that
// one case to "X"; every other page keeps its suffix.
function dedupeTitles(siteDir) {
  for (const f of walk(siteDir, ".html")) {
    const html = fs.readFileSync(f, "utf8");
    const out = html.replace(/(<title>|<meta property="og:title" content=")([^<"]+) - \2(<\/title>|")/g, "$1$2$3");
    if (out !== html) fs.writeFileSync(f, out);
  }
}

// ------------------------------------------------------------------- page enhancements

// The theme renders pages with React, which replaces the static HTML on load, so edits to
// the built HTML are discarded (measured 2026-10-21). These are applied in the browser
// instead, by one small script added to every page after the build. Each step is
// idempotent and re-run when React re-renders.
//   - proofs: "Proof (of Theorem 1)" -> "Proof of Theorem 1"; clicking a proof's header
//     folds it (proofs start open)
//   - results: a [↓] after the heading of a result whose proof is not directly below it
//   - Lean code (MyST code blocks under an entry): collapsed behind a bar, copy button kept
const ENHANCE_SCRIPT = `(function(){
function proofs(){
  document.querySelectorAll(".myst-proof.border-myst-proof").forEach(function(box){
    var title=box.querySelector(".myst-proof-title"), head=box.querySelector(".myst-proof-header"), body=box.querySelector(".myst-proof-body");
    if(!title||!head||!body) return;
    if(!title.dataset.lemmata){
      title.dataset.lemmata="1";
      // "Proof (of X)" -> "Proof of X": the theme wraps any proof title in "(" and ")" text
      // nodes. Only text nodes are edited, so the links React rendered stay its own.
      var texts=[]; title.childNodes.forEach(function(n){ if(n.nodeType===3) texts.push(n); });
      var open=texts.find(function(n){ return /\\(\\s*$/.test(n.textContent); });
      var next=open&&open.nextSibling; while(next&&next.nodeType===8) next=next.nextSibling;   // skip React's comment markers
      if(open && next && /^\\s*of\\b/.test(next.textContent||"")){
        open.textContent=open.textContent.replace(/\\(\\s*$/,"");
        var close=texts.reverse().find(function(n){ return /^\\s*\\)\\s*$/.test(n.textContent); });
        if(close) close.textContent="";
      }
    }
    if(!head.dataset.lemmata){
      head.dataset.lemmata="1"; head.classList.add("lemmata-fold"); head.setAttribute("role","button"); head.tabIndex=0;
      head.title="Fold or unfold the proof";
      var toggle=function(e){ if(e.target.closest("a")) return; box.classList.toggle("lemmata-folded"); };
      head.addEventListener("click",toggle);
      head.addEventListener("keydown",function(e){ if(e.key==="Enter"||e.key===" "){ e.preventDefault(); toggle(e); } });
    }
  });
}
function proofLinks(){
  // For each proof that names results, add [↓] to those results' headings unless the
  // proof directly follows them.
  document.querySelectorAll(".myst-proof.border-myst-proof").forEach(function(box, i){
    if(!box.id) box.id="lemmata-proof-"+(i+1);
    box.querySelectorAll(".myst-proof-title a[href^='#']").forEach(function(a){
      var res=document.getElementById(a.getAttribute("href").slice(1));
      if(!res||res===box) return;
      var head=res.querySelector(".myst-proof-title"); if(!head||head.querySelector(".lemmata-to-proof[href='#"+box.id+"']")) return;
      if(res.nextElementSibling===box) return;
      var down=document.createElement("a"); down.className="lemmata-to-proof"; down.href="#"+box.id; down.textContent="[↓]";
      down.title="Go to the proof"; head.append(" ",down);
    });
  });
}
function lean(){
  // The Lean is a literalinclude of a .lean file, shown with its filename in the block's
  // header (MyST highlights it as plain text, so there is no language class to match).
  document.querySelectorAll("article .myst-code").forEach(function(code){
    if(code.dataset.lemmata) return;
    var head=code.firstElementChild; if(!head||!/\\.lean\\s*$/.test(head.textContent||"")) return;
    code.dataset.lemmata="1";
    var d=document.createElement("details"); d.className="lemmata-lean";
    var s=document.createElement("summary"); var lines=(code.textContent.match(/\\n/g)||[]).length+1;
    s.textContent="Lean source: "+head.textContent.trim()+" ("+lines+" lines)"; d.append(s);
    code.parentNode.insertBefore(d,code); d.append(code);
  });
}
function run(){ try{ proofs(); proofLinks(); lean(); }catch(e){} }
// Only after React has hydrated: changing the DOM before that is a hydration mismatch
// (React error #418), after which React re-renders and drops the changes. Then re-apply
// whenever React re-renders.
function start(){
  setTimeout(function(){
    run();
    var t=null; new MutationObserver(function(){ clearTimeout(t); t=setTimeout(run,50); }).observe(document.body,{childList:true,subtree:true});
  },300);
}
if(document.readyState==="complete") start(); else window.addEventListener("load",start);
})();`;
function injectEnhancements(siteDir) {
  const tag = `<script data-lemmata-enhance>${ENHANCE_SCRIPT}</script>`;
  let n = 0;
  for (const f of walk(siteDir, ".html")) {
    const html = fs.readFileSync(f, "utf8");
    if (html.includes("data-lemmata-enhance") || !html.includes("</body>")) continue;
    fs.writeFileSync(f, html.replace("</body>", tag + "</body>")); n++;
  }
  return n;
}

// ------------------------------------------------------------------------- analytics

// Privacy-friendly analytics (Plausible), added to every page's <head> after the build.
// The theme's own analytics_plausible option is hard-wired to plausible.io, so it cannot
// point at a self-hosted instance. The script URL comes from the cluster (ANALYTICS_SCRIPT,
// a trusted setting); without it nothing is added, so local builds and previews are not
// tracked. The URL must be https and is checked before it is written into HTML.
function injectAnalytics(siteDir, scriptUrl) {
  if (!scriptUrl) return 0;
  let u; try { u = new URL(scriptUrl); } catch { fail(`ANALYTICS_SCRIPT is not a URL: ${scriptUrl}`); return 0; }
  if (u.protocol !== "https:" || /["'<>\s]/.test(scriptUrl)) { fail(`ANALYTICS_SCRIPT must be a plain https URL`); return 0; }
  // transformRequest strips a release prefix (/_releases/<id>) from the page URL and the
  // referrer, so statistics are per stable page (/implication-composition), not split anew
  // with every release. A no-op for releases built for the site root (pins.json
  // release_prefix: false), whose pages are already at their stable URLs.
  const strip = "function(u){return u&&u.replace(/\\/_releases\\/[^/]+(?=\\/|$)/,'')}";
  const snippet = `<script async src="${scriptUrl}"></script>` +
    `<script>window.plausible=window.plausible||function(){(plausible.q=plausible.q||[]).push(arguments)},` +
    `plausible.init=plausible.init||function(i){plausible.o=i||{}};` +
    `plausible.init({transformRequest:function(e){var s=${strip};e.u=s(e.u);if(e.r)e.r=s(e.r);return e}})</script>`;
  let n = 0;
  for (const f of walk(siteDir, ".html")) {
    const html = fs.readFileSync(f, "utf8");
    if (html.includes(scriptUrl) || !html.includes("</head>")) continue;
    fs.writeFileSync(f, html.replace("</head>", snippet + "</head>"));
    n++;
  }
  return n;
}

// ------------------------------------------------------------------------------- main

const [cmd, ...args] = process.argv.slice(2);
const flag = (name) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : undefined; };
switch (cmd) {
  case "validate": {
    const ms = loadManifests(); checkSnippets(ms); checkDois(ms); checkUmbrella(false);
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
  case "doi": { const ms = loadManifests(); finish(); await fetchDois(ms); finish(); break; }
  case "site-index": {            // after myst build: llms.txt, lemmata.json, sitemap, robots
    const cats = loadCategories(); const ms = loadManifests(cats); finish();
    const report = args[0] ? JSON.parse(fs.readFileSync(args[0], "utf8")) : null;
    siteIndex(ms, cats, report, args[1], { commit: flag("--commit"), sourceUrl: flag("--source-url") });
    finish(`wrote llms.txt, lemmata.json, sitemap.xml, robots.txt to ${args[1]}`); break;
  }
  case "enhance": {               // after the build: proof titles, folding, Lean collapsing
    finish(`page enhancements added to ${injectEnhancements(args[0])} page(s)`); break;
  }
  case "analytics": {             // after the build: add the analytics snippet to every page
    const n = injectAnalytics(args[0], process.env.ANALYTICS_SCRIPT ?? "");
    finish(process.env.ANALYTICS_SCRIPT ? `analytics added to ${n} page(s)` : "no ANALYTICS_SCRIPT: no analytics"); break;
  }
  case "provenance": {            // what the controller ships for HEAD, from local git
    const ms = loadManifests(); finish();
    process.stdout.write(JSON.stringify(loadProvenance(ms, null), null, 2) + "\n"); break;
  }
  default:
    console.error("usage: lemmata.mjs validate | umbrella [--write] | request <out> | prepare <report.json>|--preview [--commit SHA] [--source-url URL] | new <id> <LeanName> <category>");
    process.exit(2);
}
