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
  const url = decodeURIComponent(new URL(req.url, "http://x").pathname);
  if (!url.startsWith(base + "/")) { res.writeHead(404).end(); return; }
  let p = path.join(root, url.slice(base.length));
  if (!p.startsWith(root)) { res.writeHead(403).end(); return; }
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
page.on("console", (m) => { if (m.type() === "error") errors.push(`console: ${m.text()}`); });
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
check(await page.getByText("✓ checked").count() === 2, "verification panel shows two checked results");
const widget = page.locator(".lemmata-chain");
await widget.waitFor({ timeout: 15000 }).catch(() => {});
check(await widget.count() === 1, "anywidget loads");
if (await widget.count()) {
  check((await widget.locator("p").textContent()).includes("R follows"), "widget initial state");
  await widget.locator("input").nth(2).uncheck();
  check((await widget.locator("p").textContent()).includes("cannot reach R"), "widget reacts to input");
}
// Cross-page reference: clicking the link to the other entry's theorem navigates there.
await page.locator("a", { hasText: "self-implication" }).first().click();
await page.waitForURL(/self-implication/, { timeout: 10000 }).catch(() => {});
check(page.url().includes(`${base}/self-implication`), `cross-reference navigates inside the release (${page.url().replace(origin, "")})`);
check(await page.locator("#thm-self-implication").count() === 1, "target theorem anchor exists");

// Direct load of a deep page, not via client-side navigation.
const resp = await page.goto(`${origin}${base}/self-implication/`, { waitUntil: "networkidle" });
check(resp.status() === 200, "deep page loads directly");

check(errors.length === 0, `no console errors or failed requests${errors.length ? ":\n  " + errors.join("\n  ") : ""}`);
await browser.close(); server.close();
process.exit(failures.length ? 1 : 0);
