// Browser smoke test for a rendered site. Serves <html-dir> as plain static files under
// <base> (exactly what production nginx does) and checks that a reader actually sees math,
// Mermaid, cross-references, the widget, and the verification panel -- with no console
// errors and no failed requests.
//
//   node tests/browser.mjs <html-dir> <base>      e.g. docs/_build/html /_releases/test
import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import { chromium } from "playwright";

const [dir, base = ""] = process.argv.slice(2);
const root = path.resolve(dir);
const types = { ".html": "text/html", ".js": "text/javascript", ".mjs": "text/javascript",
  ".css": "text/css", ".json": "application/json", ".svg": "image/svg+xml", ".woff2": "font/woff2",
  ".png": "image/png", ".ico": "image/x-icon", ".xml": "application/xml", ".txt": "text/plain" };
const server = http.createServer((req, res) => {
  // A malformed escape (%E0%A4%A) is a bad request, not a crash of the test server.
  let url;
  try { url = decodeURIComponent(new URL(req.url, "http://x").pathname); } catch { res.writeHead(400).end(); return; }
  if (!url.startsWith(base + "/")) { res.writeHead(404).end(); return; }
  let p = path.join(root, url.slice(base.length));
  // Inside root itself, not a sibling that shares its prefix (/tmp/site vs /tmp/site-x).
  if (p !== root && !p.startsWith(root + path.sep)) { res.writeHead(403).end(); return; }
  if (fs.existsSync(p) && fs.statSync(p).isDirectory()) p = path.join(p, "index.html");
  else if (!fs.existsSync(p) && fs.existsSync(p + ".html")) p += ".html";
  if (!fs.existsSync(p)) { res.writeHead(404).end(); return; }
  res.writeHead(200, { "content-type": types[path.extname(p)] ?? "application/octet-stream" });
  fs.createReadStream(p).pipe(res);
}).listen(0, "127.0.0.1");
await new Promise((r) => server.once("listening", r));
const origin = `http://127.0.0.1:${server.address().port}`;

const failures = [];
const check = (cond, msg) => { console.log(`${cond ? "ok  " : "FAIL"} ${msg}`); if (!cond) failures.push(msg); };

const browser = await chromium.launch();
const page = await browser.newPage();
const errors = [];
// giscus (comments) runs in its own frame and logs a 404 for a thread or giscus.json that
// does not exist yet; that is its normal state, not a site error.
page.on("console", (m) => { if (m.type() === "error" && !/giscus\.app/.test(m.location()?.url ?? "")) errors.push(`console: ${m.text()}`); });
page.on("pageerror", (e) => errors.push(`pageerror: ${e.message}`));
page.on("requestfailed", (r) => errors.push(`requestfailed: ${r.url()}`));
page.on("response", (r) => { if (r.status() >= 400 && r.url().startsWith(origin)) errors.push(`HTTP ${r.status()} ${r.url()}`); });

await page.goto(`${origin}${base}/`, { waitUntil: "networkidle" });
check(await page.locator("h1", { hasText: "Lemmata" }).count() > 0, "landing page renders");
check(await page.locator("table a", { hasText: "Composition of implications" }).count() === 1, "catalog lists entries");

await page.goto(`${origin}${base}/implication-composition/`, { waitUntil: "networkidle" });
check(await page.locator(".katex").count() >= 3, "KaTeX renders inline and display math");
check(await page.locator("pre code", { hasText: "theorem implication_composition" }).count() > 0, "Lean snippet included from lean/");
await page.waitForSelector("svg[id^=mermaid], .mermaid svg, [class*=mermaid] svg", { timeout: 15000 }).catch(() => {});
check(await page.locator("svg[id^=mermaid], .mermaid svg, [class*=mermaid] svg").count() > 0, "Mermaid diagram renders");
check(await page.getByText(/✓ kernel-checked/).count() === 2, "verification panel shows two kernel-checked results");
check(await page.locator("a", { hasText: 'What "checked" means' }).count() >= 1, "verification panel links to the 'checked' page");
check(!(await page.locator("body").innerText()).includes("axioms: propext"), "panel no longer lists axioms");
check(await page.locator(".lemmata-header").count() === 1, "header block present");
check(await page.locator(".lemmata-header .lemmata-abstract").count() === 1, "abstract shown under the header");
// Applied by the page script after React has hydrated.
await page.waitForFunction(() => document.querySelector("details.lemmata-lean"), null, { timeout: 10000 }).catch(() => {});
check(await page.locator("details.lemmata-lean:not([open])").count() >= 1, "Lean source starts collapsed");
check(await page.locator("details.lemmata-verification:not([open]), .lemmata-verification details:not([open])").count() >= 1
  || await page.locator(".lemmata-verification").count() >= 1, "verification panel is collapsible");
const proofTitles = await page.locator(".myst-proof.border-myst-proof .myst-proof-title").allTextContents();
check(proofTitles.length > 0 && proofTitles.every((t) => /^Proof\s+of\b/.test(t.trim()) && !t.includes("(")), "proof titles read 'Proof of ...'");
check((await page.locator(".myst-primary-sidebar-toc .myst-toc > div").evaluateAll((xs) => xs.filter((x) => x.offsetParent).length)) === 0,
  "sidebar lists no entries or categories");
// Lean next to each result: every box placed directly under the result it belongs to.
const placement = await page.evaluate(() => { const bs = [...document.querySelectorAll(".lemmata-lean-for")];
  return { n: bs.length, ok: bs.filter((b) => b.classList.contains("lemmata-placed") &&
    b.previousElementSibling?.id === b.className.match(/lemmata-for-(\S+)/)[1]).length }; });
check(placement.n > 0 && placement.ok === placement.n, `Lean box under each result (${placement.ok}/${placement.n})`);
const widget = page.locator(".lemmata-chain");
await widget.waitFor({ timeout: 15000 }).catch(() => {});
check(await widget.count() === 1, "anywidget loads");
if (await widget.count()) {
  check((await widget.locator("p").textContent()).includes("R follows"), "widget initial state");
  await widget.locator("input").nth(2).uncheck();
  check((await widget.locator("p").textContent()).includes("cannot reach R"), "widget reacts to input");
}
// Cross-page navigation: from a category page to an entry, client-side, staying inside
// the release, and landing on the entry's theorem anchor.
await page.goto(`${origin}${base}/c/logic/`, { waitUntil: "networkidle" });
await page.locator("table a", { hasText: "Composition of implications" }).first().click();
await page.waitForURL(/implication-composition/, { timeout: 10000 }).catch(() => {});
check(page.url().includes(`${base}/implication-composition`), `category link navigates inside the release (${page.url().replace(origin, "")})`);
check(await page.locator("#thm-implication-composition").count() === 1, "target theorem anchor exists");

// Direct load of a deep page, not via client-side navigation.
const resp = await page.goto(`${origin}${base}/implication-composition/`, { waitUntil: "networkidle" });
check(resp.status() === 200, "deep page loads directly");

// The "What checked means" subpage exists.
const ck = await page.goto(`${origin}${base}/checked/`, { waitUntil: "networkidle" });
check(ck.status() === 200 && (await page.locator("h1").first().textContent()).includes("checked"), "'checked' subpage renders");

// Follow every same-site link on every page, both as a fresh page load and as the
// href the browser actually resolved. Counting links is not enough: the catalog's links
// once rendered as raw "../x/index.md" hrefs that 404'd (2026-10-19).
const LIMIT = 2000;                       // a runaway guard, reported if reached (was a silent 200)
const seen = new Set(), queue = [`${origin}${base}/`], broken = [];
const anchors = new Map();                 // page URL -> Set of #ids linked to it
while (queue.length && seen.size < LIMIT) {
  const url = queue.shift().split("#")[0];
  if (seen.has(url)) continue;
  seen.add(url);
  const r = await page.goto(url, { waitUntil: "domcontentloaded" });
  if (!r || r.status() >= 400) { broken.push(`${r?.status()} ${url}`); continue; }
  for (const href of await page.locator("a[href]").evaluateAll((as) => as.map((a) => a.href))) {
    if (!href.startsWith(origin)) continue;
    if (!href.startsWith(`${origin}${base}/`)) { broken.push(`outside the release: ${href} (on ${url})`); continue; }
    if (/\.(md|json|zip|pdf|txt|xml|ico)$/.test(new URL(href).pathname)) {
      if (/\.md$/.test(new URL(href).pathname)) broken.push(`raw .md link: ${href} (on ${url})`);
      continue;
    }
    // Remember the anchor, checked once its page is loaded (below); fragments used to be
    // dropped, so a link to a missing #id passed.
    const [target, frag] = href.split("#");
    if (frag) { if (!anchors.has(target)) anchors.set(target, new Set()); anchors.get(target).add(decodeURIComponent(frag)); }
    queue.push(href);
  }
}
if (queue.length && seen.size >= LIMIT) broken.push(`crawl stopped at ${LIMIT} pages with ${queue.length} links left unchecked`);
// Every #anchor that some page links to must exist on its target page. MyST renders the
// page with React, so wait until it has loaded before looking for the ids.
for (const [target, ids] of anchors) {
  if (!seen.has(target)) continue;                                 // its own failure is reported above
  await page.goto(target, { waitUntil: "load" });
  await page.waitForTimeout(300);
  const missing = await page.evaluate((list) => list.filter((id) => !document.getElementById(id)), [...ids]);
  for (const id of missing) broken.push(`missing anchor #${id} on ${target}`);
}
check(broken.length === 0, `all ${seen.size} internal pages, links and ${[...anchors.values()].reduce((n, x) => n + x.size, 0)} anchors resolve${broken.length ? ":\n  " + broken.join("\n  ") : ""}`);

check(errors.length === 0, `no console errors or failed requests${errors.length ? ":\n  " + errors.join("\n  ") : ""}`);
await browser.close(); server.close();
process.exit(failures.length ? 1 : 0);
