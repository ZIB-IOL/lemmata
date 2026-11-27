// Oracle methods on smooth bodies C = K + B_r, for f(x) = ½‖x − c‖² (L = 1).
// Panel "planar": a planar core K (point, segment, triangle, ellipse) rounded by a disk; drag the
// target c. Vanilla Frank–Wolfe uses C's oracle; the quadratic method (Theorem: matching upper
// bound) runs Frank–Wolfe on K and lifts by the ball; the joint method (Theorem: linear rate) uses
// exact line search on K. Panel "hard": a hidden instance of the hard family in dimension 256k+1
// with the vertex oracle, a barycenter oracle, or the unique oracle of a jittered body.
// Everything runs in the browser; it uses only model.get/set/on (no kernel).

const add = (a, b) => [a[0] + b[0], a[1] + b[1]];
const sub = (a, b) => [a[0] - b[0], a[1] - b[1]];
const mul = (a, s) => [a[0] * s, a[1] * s];
const dot = (a, b) => a[0] * b[0] + a[1] * b[1];
const norm = (a) => Math.hypot(a[0], a[1]);
const clip = (v, r) => { const n = norm(v); return n <= r ? v : mul(v, r / n); };
export const R_BALL = 0.45;

function segProj(c, p, q) {
  const d = sub(q, p), L = dot(d, d);
  const t = L > 0 ? Math.min(1, Math.max(0, dot(sub(c, p), d) / L)) : 0;
  return add(p, mul(d, t));
}
function polygon(pts) {
  const inside = (c) => pts.every((p, i) => {
    const q = pts[(i + 1) % pts.length];
    return (q[0] - p[0]) * (c[1] - p[1]) - (q[1] - p[1]) * (c[0] - p[0]) >= -1e-12;
  });
  return {
    lmo: (g) => pts.reduce((b, p) => (dot(g, p) < dot(g, b) - 1e-15 ? p : b), pts[0]),
    proj: (c) => {
      if (pts.length > 2 && inside(c)) return c;
      let best = null;
      pts.forEach((p, i) => {
        if (pts.length === 2 && i === 1) return;
        const z = segProj(c, p, pts[(i + 1) % pts.length]);
        if (!best || norm(sub(z, c)) < norm(sub(best, c))) best = z;
      });
      return best;
    },
    diam: Math.max(...pts.flatMap((p) => pts.map((q) => norm(sub(p, q))))),
  };
}
function ellipse(ax, ay) {
  return {
    lmo: (g) => { const s = Math.hypot(ax * g[0], ay * g[1]);
      return s === 0 ? [ax, 0] : [-ax * ax * g[0] / s, -ay * ay * g[1] / s]; },
    proj: (c) => {
      if ((c[0] / ax) ** 2 + (c[1] / ay) ** 2 <= 1) return c;
      const at = (t) => [c[0] * ax * ax / (ax * ax + t), c[1] * ay * ay / (ay * ay + t)];
      let lo = 0, hi = 1;
      while ((at(hi)[0] / ax) ** 2 + (at(hi)[1] / ay) ** 2 > 1) hi *= 2;
      for (let i = 0; i < 80; i++) {
        const m = (lo + hi) / 2, z = at(m);
        if ((z[0] / ax) ** 2 + (z[1] / ay) ** 2 > 1) lo = m; else hi = m;
      }
      return at(hi);
    },
    diam: 2 * ax,
    outer: ax * ax / ay, // largest radius of curvature of K
  };
}
export const CORES = {
  point: { name: "disk", ...polygon([[0, 0]]), outer: 0 },
  segment: { name: "stadium", ...polygon([[-0.75, 0], [0.75, 0]]) },
  triangle: { name: "rounded triangle", ...polygon([[-0.75, -0.45], [0.75, -0.45], [0, 0.7]]) },
  ellipse: { name: "rounded ellipse", ...ellipse(0.7, 0.4) },
};
CORES.point.diam = 0;

/** Gaps after t oracle calls, t = 0..T, for the three methods on K + B_r, target c. */
export function simulatePlanar(coreKey, c, T) {
  const K = CORES[coreKey], r = R_BALL;
  const lmoC = (q) => { const n = norm(q); return n === 0 ? add(K.lmo([0, 1]), [0, -r])
    : sub(K.lmo(q), mul(q, r / n)); };
  const pk = K.proj(c), dist = Math.max(0, norm(sub(c, pk)) - r), fstar = 0.5 * dist * dist;
  const gap = (x) => Math.max(0, 0.5 * dot(sub(x, c), sub(x, c)) - fstar);
  const lift = (a) => add(a, clip(sub(c, a), r));
  const e = [0, 1];
  // vanilla Frank–Wolfe with short steps, started at the body's oracle answer for e
  const fw = [], fwPath = [];
  let x = lmoC(e);
  fw.push(gap(x)); fwPath.push(x);
  for (let t = 1; t <= T; t++) {
    const g = sub(x, c), v = lmoC(g), d = sub(x, v), dd = dot(d, d);
    const gam = dd > 0 ? Math.min(1, Math.max(0, dot(g, d) / dd)) : 0;
    x = sub(x, mul(d, gam)); fw.push(gap(x)); fwPath.push(x);
  }
  // quadratic method: one call for a core point, then Frank–Wolfe 2/(j+2) on K, lifted
  const qm = [], qmPath = [];
  let a = add(lmoC(e), mul(e, r));
  qm.push(gap(lift(a))); qmPath.push(lift(a));
  for (let j = 0; j < T; j++) {
    const g = sub(lift(a), c);
    const s = norm(g) === 0 ? a : K.lmo(g);
    a = add(mul(a, 1 - 2 / (j + 2)), mul(s, 2 / (j + 2)));
    qm.push(gap(lift(a))); qmPath.push(lift(a));
  }
  // joint method: exact line search on K for ½‖a − c‖², lifted
  const jm = [], jmPath = [];
  const x0 = lmoC(e), q0 = sub(x0, c);
  a = norm(q0) === 0 ? x0 : add(lmoC(q0), mul(q0, r / norm(q0)));
  const first = norm(q0) === 0 ? x0 : lmoC(q0);
  jm.push(gap(first)); jmPath.push(first);
  for (let t = 1; t <= T; t++) {
    const q = sub(a, c);
    if (norm(q) > r) {
      const s = K.lmo(q), G = dot(q, sub(a, s)), H = dot(sub(s, a), sub(s, a));
      const lam = H > 0 ? Math.min(1, Math.max(0, G / H)) : 1;
      a = add(a, mul(sub(s, a), lam));
    }
    jm.push(gap(lift(a))); jmPath.push(lift(a));
  }
  const D = K.diam + 2 * r;
  let rate = null;
  if (K.outer !== undefined) {
    const R = r + K.outer, cc = R === r ? 1 : 0.5 * Math.min(1, r / (2 * (R - r)));
    rate = (t) => (1 - cc) ** t * D * D / 2;
  }
  return { fw, qm, jm, fwPath, qmPath, jmPath, delta: K.diam, D, rate, xstar: lift(pk), lmoC };
}

function mulberry(seed) {
  return () => { seed |= 0; seed = (seed + 0x6d2b79f5) | 0; let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}
function projSimplex(v) {
  const u = [...v].sort((p, q) => q - p);
  let css = 0, th = 0;
  for (let i = 0; i < u.length; i++) { css += u[i]; const t = (css - 1) / (i + 1); if (u[i] - t > 0) th = t; }
  return v.map((x) => Math.max(0, x - th));
}

/** The hard family with a = r = 1: gaps after t calls for vanilla FW, the quadratic method and
 * probe-then-exploit, with the vertex, barycenter or unique (jittered) oracle. */
export function simulateHard(k, rule, T, seed = 7) {
  const N = 256 * k, d = 8 * k, rnd = mulberry(seed);
  const labels = [0], pool = Array.from({ length: N - 1 }, (_, i) => i + 1);
  for (let i = 0; i < d - 1; i++) labels.push(pool.splice(Math.floor(rnd() * pool.length), 1)[0]);
  labels.sort((p, q) => p - q);
  const xi = labels.map(() => 0.02 * (2 * rnd() - 1)), zeta = labels.map(() => 0.02 * (2 * rnd() - 1));
  const s = 1e-4;
  const oracle = (qx, qy) => {
    const nq = Math.hypot(qy, Math.hypot(...qx));
    const x = new Float64Array(N);
    if (nq === 0) { x[0] = 1; return [x, 0]; }
    if (rule === "unique") {
      const g = labels.map((j, m) => (qx[j] * (1 + xi[m]) + qy * (1 + zeta[m])) / nq);
      const u = projSimplex(g.map((v) => -v / (2 * s)));
      let hy = 0, uu = 0;
      labels.forEach((j, m) => { x[j] += u[m] * (1 + xi[m]); hy += u[m] * (1 + zeta[m]); uu += u[m] * u[m]; });
      const rad = s * (1 - uu) + 1;
      for (let i = 0; i < N; i++) x[i] -= rad * qx[i] / nq;
      return [x, hy - rad * qy / nq];
    }
    let mn = Infinity;
    for (const j of labels) mn = Math.min(mn, qx[j]);
    const J = rule === "barycenter" ? labels.filter((j) => qx[j] === mn) : [labels.find((j) => qx[j] === mn)];
    for (const j of J) x[j] += 1 / J.length;
    for (let i = 0; i < N; i++) x[i] -= qx[i] / nq;
    return [x, 1 - qy / nq];
  };
  let H = Math.sqrt(1 / d + 33 * 33);
  if (rule === "unique") {
    // distance from c = (0, -32) to the jittered core: minimize a convex function of the weights
    const phi = (u) => { let q = 0, h = 32, uu = 0;
      labels.forEach((_, m) => { q += (u[m] * (1 + xi[m])) ** 2; h += u[m] * (1 + zeta[m]); uu += u[m] ** 2; });
      return [Math.sqrt(q + h * h), h, uu]; };
    let u = labels.map(() => 1 / d);
    for (let it = 1; it <= 4000; it++) {
      const [nrm, h] = phi(u);
      const grad = labels.map((_, m) => (u[m] * (1 + xi[m]) ** 2 + h * (1 + zeta[m])) / nrm + 2 * s * u[m]);
      u = projSimplex(u.map((v, m) => v - (0.5 / Math.sqrt(it)) * grad[m]));
    }
    const [nrm, , uu] = phi(u);
    H = nrm - s * (1 - uu);
  }
  const fstar = 0.5 * (H - 1) ** 2 - 0.5 * 32 * 32;
  const f = (x, y) => { let q = y * y; for (let i = 0; i < N; i++) q += x[i] * x[i]; return 0.5 * q + 32 * y; };
  const gap = (x, y) => Math.max(1e-14, f(x, y) - fstar);
  // vanilla Frank–Wolfe with short steps from the start point (e_1, 0)
  const fw = [];
  let x = new Float64Array(N), y = 0; x[0] = 1; fw.push(gap(x, y));
  for (let t = 1; t <= T; t++) {
    const [vx, vy] = oracle(x, y + 32);
    let gd = (y + 32) * (y - vy), dd = (y - vy) ** 2;
    for (let i = 0; i < N; i++) { gd += x[i] * (x[i] - vx[i]); dd += (x[i] - vx[i]) ** 2; }
    const gam = dd > 0 ? Math.min(1, Math.max(0, gd / dd)) : 0;
    for (let i = 0; i < N; i++) x[i] -= gam * (x[i] - vx[i]);
    y -= gam * (y - vy); fw.push(gap(x, y));
  }
  // quadratic method; the first call is the vertical direction
  const center = [new Float64Array(N), -32];
  const lift = (ax, ay) => {
    const dx = ax.map((v) => -v), dy = center[1] - ay, n = Math.hypot(dy, Math.hypot(...dx));
    const sc = n <= 1 ? 1 : 1 / n;
    return [ax.map((v, i) => v + sc * dx[i]), ay + sc * dy];
  };
  const qm = [], probe = [];
  let [ax, ay] = oracle(new Float64Array(N), 1); ay += 1;
  const revealed = rule === "barycenter";
  let [lx, ly] = lift(ax, ay);
  qm.push(gap(lx, ly)); probe.push(gap(lx, ly));
  for (let j = 0; j < T; j++) {
    const gx = lx, gy = ly + 32;
    let [vx, vy] = oracle(gx, gy);
    const ng = Math.hypot(gy, Math.hypot(...gx));
    if (ng > 0) { for (let i = 0; i < N; i++) vx[i] += gx[i] / ng; vy += gy / ng; }
    const gam = 2 / (j + 2);
    ax = ax.map((v, i) => (1 - gam) * v + gam * vx[i]); ay = (1 - gam) * ay + gam * vy;
    [lx, ly] = lift(ax, ay);
    qm.push(gap(lx, ly)); probe.push(revealed ? 1e-14 : gap(lx, ly));
  }
  return { fw, qm, probe, k, d, N, lower: 1 / (16 * k), delta: Math.SQRT2 };
}

function elt(tag, cls, text) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text != null) e.textContent = text;
  return e;
}
function setupCanvas(canvas, w, h) {
  const r = window.devicePixelRatio || 1;
  canvas.width = Math.round(w * r); canvas.height = Math.round(h * r);
  const ctx = canvas.getContext("2d"); ctx.setTransform(r, 0, 0, r, 0, 0);
  return ctx;
}
const COLORS = { fw: "#d1495b", qm: "#2e86ab", jm: "#3c9d5d", probe: "#e07a1f" };

function render({ model, el: root }) {
  const box = elt("div", "lemmata-fs");
  const rows = [elt("div", "fs-group"), elt("div", "fs-group"), elt("div", "fs-group")];
  const buttons = {};
  const button = (row, key, value, label) => {
    const b = elt("button", "fs-btn", label); b.type = "button";
    b.addEventListener("click", () => model.set(key, value));
    buttons[key + ":" + value] = b; row.append(b);
  };
  rows[0].append(elt("span", "fs-label", "Body"));
  for (const [kk, K] of Object.entries(CORES)) button(rows[0], "body", kk, K.name);
  button(rows[0], "body", "hard", "hard family");
  rows[1].append(elt("span", "fs-label", "Hard family"));
  for (const kk of [1, 2, 4, 8]) button(rows[1], "k", kk, `k = ${kk}`);
  rows[2].append(elt("span", "fs-label", "Oracle"));
  for (const [kk, lab] of [["vertex", "vertex rule"], ["barycenter", "barycenter rule"],
    ["unique", "unique (jittered)"]]) button(rows[2], "rule", kk, lab);
  const panes = elt("div", "fs-panes");
  const geo = elt("canvas", "fs-geo"), chart = elt("canvas", "fs-chart");
  geo.setAttribute("role", "img"); chart.setAttribute("role", "img");
  geo.setAttribute("aria-label", "The body, the target c and the iterates; drag to move c");
  chart.setAttribute("aria-label", "Gap against the number of oracle calls, logarithmic axes");
  panes.append(geo, chart);
  const stats = elt("p", "fs-stats");
  box.append(...rows, panes, stats);
  root.append(box);
  const W = 300, H = 300, CW = 380, CH = 300, VIEW = 1.9;
  const g = setupCanvas(geo, W, H), k = setupCanvas(chart, CW, CH);
  const toPx = (p) => [((p[0] + VIEW) / (2 * VIEW)) * W, ((VIEW - p[1]) / (2 * VIEW)) * H];
  const ink = () => getComputedStyle(box).color || "#333";

  function chartCurves(curves, guides, T) {
    const col = ink(), L = 46, R = 10, Tp = 12, B = 34, pw = CW - L - R, ph = CH - Tp - B;
    k.clearRect(0, 0, CW, CH);
    const lx = (t) => L + (Math.log10(t + 1) / Math.log10(T + 1)) * pw;
    const ymax = 1, ymin = -9;
    const ly = (y) => Tp + ((ymax - Math.log10(Math.max(y, 10 ** ymin))) / (ymax - ymin)) * ph;
    k.strokeStyle = col; k.fillStyle = col; k.font = "11px sans-serif"; k.lineWidth = 1;
    for (let e = ymin; e <= ymax; e += 2) {
      const y = ly(10 ** e); k.globalAlpha = 0.15; k.beginPath(); k.moveTo(L, y); k.lineTo(L + pw, y); k.stroke();
      k.globalAlpha = 0.8; k.fillText(`1e${e}`, 4, y + 4);
    }
    for (const t of [1, 10, 100, 1000].filter((t) => t <= T)) {
      const x = lx(t); k.globalAlpha = 0.15; k.beginPath(); k.moveTo(x, Tp); k.lineTo(x, Tp + ph); k.stroke();
      k.globalAlpha = 0.8; k.textAlign = "center"; k.fillText(String(t), Math.min(x, L + pw - 12), Tp + ph + 14);
      k.textAlign = "left";
    }
    k.globalAlpha = 0.9; k.fillText("oracle calls", L + pw - 64, Tp + ph + 28); k.fillText("gap", L + 4, Tp + 12);
    for (const [fn, label] of guides) {
      k.save(); k.setLineDash([6, 4]); k.globalAlpha = 0.6; k.beginPath();
      for (let t = 1; t <= T; t++) { const X = lx(t), Y = ly(fn(t)); t > 1 ? k.lineTo(X, Y) : k.moveTo(X, Y); }
      k.stroke(); k.restore();
      k.globalAlpha = 0.7; k.fillText(label, L + 8, ly(fn(1)) + 14);
    }
    let yl = Tp + 26;
    for (const [ys, color, label] of curves) {
      k.strokeStyle = color; k.lineWidth = 2; k.globalAlpha = 1; k.beginPath();
      ys.forEach((y, t) => { const X = lx(t), Y = ly(y); t ? k.lineTo(X, Y) : k.moveTo(X, Y); });
      k.stroke(); k.fillStyle = color; k.fillText(label, L + pw - 150, yl); yl += 14;
    }
    k.strokeStyle = col; k.fillStyle = col;
  }

  function draw() {
    for (const [kk, b] of Object.entries(buttons)) {
      const [key, v] = kk.split(":");
      b.setAttribute("aria-pressed", String(String(model.get(key)) === v));
    }
    const body = model.get("body") || "segment";
    const col = ink();
    g.clearRect(0, 0, W, H);
    if (body === "hard") {
      const kk = Number(model.get("k")) || 4, rule = model.get("rule") || "vertex", T = 300;
      const S = simulateHard(kk, rule, T);
      chartCurves([[S.fw, COLORS.fw, "vanilla FW"], [S.qm, COLORS.qm, "quadratic method"],
        [S.probe, COLORS.probe, "probe, then exploit"]],
        [[(t) => 2 * S.delta ** 2 / (t + 1), "2δ²/(t+1)"], [() => S.lower, `lower level 1/(16k)`]], T);
      g.fillStyle = col; g.font = "13px sans-serif";
      const lines = [`hidden set: ${S.d} of ${S.N} labels`, `dimension ${S.N + 1}`, ""].concat(
        rule === "barycenter"
          ? ["the vertical query returns the", "barycenter of the bottom face:", "the instance is read off",
            "after one call"]
          : ["each call reveals at most one", "hidden label"]);
      lines.forEach((l, i) => g.fillText(l, 12, 30 + 20 * i));
      stats.textContent = `after ${T} calls: vanilla FW ${S.fw[T].toExponential(1)}, quadratic ` +
        `method ${S.qm[T].toExponential(1)}, probe ${S.probe[T].toExponential(1)}`;
      return;
    }
    const c = [Number(model.get("cx")), Number(model.get("cy"))], T = 1000;
    const S = simulatePlanar(body, c, T);
    // the body, sampled through its oracle
    g.beginPath();
    for (let i = 0; i <= 180; i++) {
      const th = (2 * Math.PI * i) / 180, p = toPx(S.lmoC([-Math.cos(th), -Math.sin(th)]));
      i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]);
    }
    g.closePath(); g.fillStyle = "#2e86ab22"; g.fill(); g.strokeStyle = "#2e86ab"; g.lineWidth = 2; g.stroke();
    for (const [path, color] of [[S.fwPath, COLORS.fw], [S.qmPath, COLORS.qm]]) {
      g.strokeStyle = color; g.globalAlpha = 0.6; g.lineWidth = 1.2; g.beginPath();
      path.slice(0, 60).forEach((p, i) => { const q = toPx(p); i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1]); });
      g.stroke(); g.globalAlpha = 1;
    }
    const xs = toPx(S.xstar), cp = toPx(c);
    g.strokeStyle = col; g.beginPath(); g.arc(xs[0], xs[1], 5, 0, 2 * Math.PI); g.stroke();
    g.strokeStyle = "#e07a1f"; g.lineWidth = 2; g.beginPath(); g.arc(cp[0], cp[1], 7, 0, 2 * Math.PI); g.stroke();
    g.fillStyle = col; g.font = "13px sans-serif"; g.fillText("x⋆", xs[0] + 8, xs[1] - 6);
    g.fillStyle = "#e07a1f"; g.fillText("c", cp[0] + 9, cp[1] + 15);
    const guides = [[(t) => 2 * S.delta ** 2 / (t + 1), "2δ²/(t+1)"]];
    if (S.rate) guides.push([S.rate, "linear rate"]);
    chartCurves([[S.fw, COLORS.fw, "vanilla FW"], [S.qm, COLORS.qm, "quadratic method"],
      [S.jm, COLORS.jm, "joint method"]], S.delta > 0 ? guides : guides.slice(1), T);
    stats.textContent = `after ${T} calls: vanilla FW ${S.fw[T].toExponential(1)}, quadratic ` +
      `method ${S.qm[T].toExponential(1)}, joint method ${S.jm[T].toExponential(1)}`;
  }

  let dragging = false;
  const moveTo = (ev) => {
    if ((model.get("body") || "segment") === "hard") return;
    const r = geo.getBoundingClientRect();
    const px = ((ev.clientX - r.left) / r.width) * W, py = ((ev.clientY - r.top) / r.height) * H;
    model.set("cx", Math.round(((px / W) * 2 * VIEW - VIEW) * 1000) / 1000);
    model.set("cy", Math.round((VIEW - (py / H) * 2 * VIEW) * 1000) / 1000);
  };
  geo.addEventListener("pointerdown", (ev) => { dragging = true; geo.setPointerCapture(ev.pointerId); moveTo(ev); });
  geo.addEventListener("pointermove", (ev) => { if (dragging) moveTo(ev); });
  geo.addEventListener("pointerup", () => { dragging = false; });
  for (const key of ["body", "cx", "cy", "k", "rule"]) model.on(`change:${key}`, draw);
  draw();
}

export default { render };
