// Theorem 2.17 in the plane: f(x) = ½ (x − c)ᵀ Q (x − c) with Q = diag(1, μ), so L = 1, f is
// μ-strongly convex and gradient dominated with c² = 1/(2μ). Drag c. When the minimizer x* is in
// the interior, with the dashed ball B(x*, r) inside the region, short steps and exact line search
// converge linearly: on the semi-log chart the primal gap falls along a line, below the guarantee
// q^t L D²/2 with q = max{1 − r²/(2 L c² D²), 0}. Near the boundary r shrinks and the rate degrades;
// outside, x* is on the boundary and the theorem does not apply.

export const T_MAX = 400;
const VIEW = 1.6;
const sgn = (v) => (v < 0 ? -1 : 1);
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const dot = (a, b) => a[0] * b[0] + a[1] * b[1];
const sub = (a, b) => [a[0] - b[0], a[1] - b[1]];
const TRI = [[0, 1.3], [-1.15, -0.7], [1.15, -0.7]];
const triDiam = Math.max(...TRI.flatMap((p) => TRI.map((q) => Math.hypot(p[0] - q[0], p[1] - q[1]))));

export const REGIONS = {
  square: {
    name: "square", diam: 2 * Math.SQRT2, start: [-1, -1],
    lmo: (g) => [-sgn(g[0]), -sgn(g[1])],
    inside: (p) => Math.abs(p[0]) <= 1 && Math.abs(p[1]) <= 1,
    depth: (p) => Math.min(1 - Math.abs(p[0]), 1 - Math.abs(p[1])),
    path: (ctx, X, Y) => { ctx.rect(X(-1), Y(1), X(1) - X(-1), Y(-1) - Y(1)); },
  },
  disk: {
    name: "disk", diam: 2, start: [0, -1],
    lmo: (g) => { const n = Math.hypot(g[0], g[1]); return n === 0 ? [1, 0] : [-g[0] / n, -g[1] / n]; },
    inside: (p) => Math.hypot(p[0], p[1]) <= 1,
    depth: (p) => 1 - Math.hypot(p[0], p[1]),
    path: (ctx, X, Y) => { ctx.arc(X(0), Y(0), X(1) - X(0), 0, 2 * Math.PI); },
  },
  triangle: {
    name: "triangle", diam: triDiam, start: TRI[1],
    lmo: (g) => TRI.reduce((b, p) => (dot(g, p) < dot(g, b) ? p : b), TRI[0]),
    inside: (p) => TRI.every((a, i) => {
      const b = TRI[(i + 1) % 3];
      return (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) >= 0;
    }),
    depth: (p) => Math.min(...TRI.map((a, i) => {
      const b = TRI[(i + 1) % 3], d = sub(b, a);
      return ((d[0]) * (p[1] - a[1]) - (d[1]) * (p[0] - a[0])) / Math.hypot(d[0], d[1]);
    })),
    path: (ctx, X, Y) => { TRI.forEach((p, i) => (i ? ctx.lineTo : ctx.moveTo).call(ctx, X(p[0]), Y(p[1]))); ctx.closePath(); },
  },
};

export const RULES = {
  short: { name: "short step", color: "#d1495b" },
  ls: { name: "exact line search", color: "#2a9d8f" },
  open: { name: "open loop 2/(t+2)", color: "#8a8a8a" },
};

export function problem(regionKey, mu, c) {
  const R = REGIONS[regionKey];
  const f = (x) => 0.5 * ((x[0] - c[0]) ** 2 + mu * (x[1] - c[1]) ** 2);
  const grad = (x) => [x[0] - c[0], mu * (x[1] - c[1])];
  const curv = (d) => d[0] * d[0] + mu * d[1] * d[1];
  let xs;
  if (R.inside(c)) xs = [c[0], c[1]];
  else if (regionKey === "square") xs = [clamp(c[0], -1, 1), clamp(c[1], -1, 1)];
  else if (regionKey === "disk") {
    const at = (lam) => [c[0] / (1 + lam), (mu * c[1]) / (mu + lam)];
    let lo = 0, hi = 1;
    while (Math.hypot(...at(hi)) > 1) hi *= 2;
    for (let k = 0; k < 100; k++) { const m = (lo + hi) / 2; if (Math.hypot(...at(m)) > 1) lo = m; else hi = m; }
    xs = at(hi);
  } else {
    let best = null;
    TRI.forEach((a, i) => {
      const b = TRI[(i + 1) % 3], d = sub(b, a);
      const s = clamp(-dot(grad(a), d) / curv(d), 0, 1), p = [a[0] + s * d[0], a[1] + s * d[1]];
      if (!best || f(p) < f(best)) best = p;
    });
    xs = best;
  }
  const r = R.inside(c) ? Math.max(0, R.depth(c)) : 0;
  const L = 1, cgd2 = 1 / (2 * mu), D = R.diam;
  const q = Math.max(1 - (r * r) / (2 * L * cgd2 * D * D), 0);
  return { R, f, grad, curv, xs, fstar: f(xs), L, r, q, D, mu };
}

export function simulate(P, ruleKey, T = T_MAX) {
  const { R, f, grad, curv, fstar, L } = P;
  const xs = [R.start.slice()], H = new Float64Array(T + 1);
  let x = R.start.slice();
  H[0] = f(x) - fstar;
  for (let t = 0; t < T; t++) {
    const g = grad(x), v = R.lmo(g), d = sub(v, x), gap = -dot(g, d), dd = dot(d, d);
    let gam;
    if (ruleKey === "open") gam = 2 / (t + 2);
    else if (ruleKey === "short") gam = dd === 0 ? 0 : Math.min(1, gap / (L * dd));
    else { const qd = curv(d); gam = qd === 0 ? 0 : Math.min(1, gap / qd); }
    x = [x[0] + gam * d[0], x[1] + gam * d[1]];
    xs.push(x); H[t + 1] = Math.max(0, f(x) - fstar);
  }
  return { xs, H };
}

function el(tag, cls, text) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
}

function setupCanvas(canvas, w, h) {
  const r = window.devicePixelRatio || 1;
  canvas.width = w * r; canvas.height = h * r;
  const ctx = canvas.getContext("2d"); ctx.setTransform(r, 0, 0, r, 0, 0);
  return ctx;
}

function render({ model, el: root }) {
  const box = el("div", "lemmata-lin");
  const controls = el("div", "lin-controls");
  const group = (label) => { const g = el("div", "lin-group"); g.append(el("span", "lin-label", label)); controls.append(g); return g; };
  const btns = {};
  const gRegion = group("Region");
  for (const k of Object.keys(REGIONS)) {
    const b = el("button", "lin-btn", REGIONS[k].name); b.type = "button";
    b.addEventListener("click", () => model.set("region", k)); gRegion.append(b); btns["region:" + k] = b;
  }
  const gObj = group("Objective");
  for (const [k, name] of [["round", "round (μ = 1)"], ["elongated", "elongated (μ = 0.3)"]]) {
    const b = el("button", "lin-btn", name); b.type = "button";
    b.addEventListener("click", () => model.set("objective", k)); gObj.append(b); btns["objective:" + k] = b;
  }
  const gRun = group("Run");
  const play = el("button", "lin-btn", "pause"); play.type = "button";
  const restart = el("button", "lin-btn", "restart"); restart.type = "button";
  gRun.append(play, restart);
  const panes = el("div", "lin-panes");
  const geo = el("canvas", "lin-geo"), chart = el("canvas", "lin-chart");
  panes.append(geo, chart);
  const stats = el("p", "lin-stats"), verdict = el("p", "lin-verdict");
  box.append(controls, panes, stats, verdict);
  root.append(box);
  const gctx = setupCanvas(geo, 300, 300), cctx = setupCanvas(chart, 370, 300);
  let P = null, runs = {}, t = 0, playing = true, raf = null;
  const fg = () => getComputedStyle(root).color || "#333";
  const X = (u) => ((u + VIEW) / (2 * VIEW)) * 300, Y = (u) => ((VIEW - u) / (2 * VIEW)) * 300;

  function start() {
    const region = REGIONS[model.get("region")] ? model.get("region") : "disk";
    const mu = model.get("objective") === "elongated" ? 0.3 : 1;
    P = problem(region, mu, [model.get("cx"), model.get("cy")]);
    runs = {};
    for (const k of Object.keys(RULES)) runs[k] = simulate(P, k);
    t = 0;
    for (const [key, b] of Object.entries(btns)) {
      const [kind, k] = key.split(":");
      b.setAttribute("aria-pressed", (kind === "region" ? k === region : k === (mu === 1 ? "round" : "elongated")) ? "true" : "false");
    }
    draw();
  }

  function drawGeometry() {
    const ctx = gctx;
    ctx.clearRect(0, 0, 300, 300);
    ctx.beginPath(); P.R.path(ctx, X, Y);
    ctx.fillStyle = "rgba(136,136,136,0.16)"; ctx.fill();
    ctx.strokeStyle = "rgba(136,136,136,0.8)"; ctx.lineWidth = 1.2; ctx.stroke();
    if (P.r > 0) {
      ctx.setLineDash([4, 3]); ctx.strokeStyle = fg(); ctx.globalAlpha = 0.6; ctx.beginPath();
      ctx.arc(X(P.xs[0]), Y(P.xs[1]), (P.r / (2 * VIEW)) * 300, 0, 2 * Math.PI); ctx.stroke();
      ctx.setLineDash([]); ctx.globalAlpha = 1;
    }
    for (const k of Object.keys(RULES)) {
      const xs = runs[k].xs, n = Math.min(t, xs.length - 1);
      ctx.beginPath(); ctx.strokeStyle = RULES[k].color; ctx.globalAlpha = 0.75; ctx.lineWidth = 1;
      for (let i = 0; i <= n; i++) (i ? ctx.lineTo : ctx.moveTo).call(ctx, X(xs[i][0]), Y(xs[i][1]));
      ctx.stroke(); ctx.globalAlpha = 1;
      ctx.beginPath(); ctx.fillStyle = RULES[k].color; ctx.arc(X(xs[n][0]), Y(xs[n][1]), 3.2, 0, 2 * Math.PI); ctx.fill();
    }
    const c = [model.get("cx"), model.get("cy")];
    ctx.strokeStyle = fg(); ctx.fillStyle = fg(); ctx.lineWidth = 1.5; ctx.font = "12px sans-serif";
    ctx.beginPath(); ctx.moveTo(X(c[0]) - 5, Y(c[1]) - 5); ctx.lineTo(X(c[0]) + 5, Y(c[1]) + 5);
    ctx.moveTo(X(c[0]) - 5, Y(c[1]) + 5); ctx.lineTo(X(c[0]) + 5, Y(c[1]) - 5); ctx.stroke();
    ctx.fillText("c", X(c[0]) + 7, Y(c[1]) - 6);
    ctx.beginPath(); ctx.arc(X(P.xs[0]), Y(P.xs[1]), 4, 0, 2 * Math.PI); ctx.lineWidth = 1.2; ctx.stroke();
    ctx.fillText("x*", X(P.xs[0]) + 6, Y(P.xs[1]) + 14);
  }

  function drawChart() {
    const ctx = cctx, W = 370, Hh = 300, ml = 44, mr = 8, mt = 10, mb = 30;
    ctx.clearRect(0, 0, W, Hh);
    const ly0 = -16, ly1 = 1;
    const px = (s) => ml + (s / T_MAX) * (W - ml - mr);
    const py = (h) => mt + ((ly1 - Math.log10(Math.max(h, 10 ** ly0))) / (ly1 - ly0)) * (Hh - mt - mb);
    ctx.strokeStyle = "rgba(136,136,136,0.35)"; ctx.fillStyle = fg(); ctx.font = "11px sans-serif"; ctx.lineWidth = 1;
    for (let e = ly0; e <= ly1; e += 2) {
      ctx.beginPath(); ctx.moveTo(ml, py(10 ** e)); ctx.lineTo(W - mr, py(10 ** e)); ctx.stroke();
      ctx.fillText("1e" + e, 4, py(10 ** e) + 4);
    }
    for (let s = 0; s <= T_MAX; s += 100) {
      ctx.beginPath(); ctx.moveTo(px(s), mt); ctx.lineTo(px(s), Hh - mb); ctx.stroke();
      ctx.fillText(String(s), px(s) - 8, Hh - mb + 14);
    }
    ctx.fillText("t", W - mr - 8, Hh - 4);
    if (P.r > 0) {
      const g0 = (P.L * P.D * P.D) / 2;
      ctx.setLineDash([5, 4]); ctx.strokeStyle = fg(); ctx.globalAlpha = 0.6; ctx.beginPath();
      for (let s = 0; s <= T_MAX; s += 2) (s ? ctx.lineTo : ctx.moveTo).call(ctx, px(s), py(g0 * P.q ** s));
      ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha = 1;
      ctx.fillText("qᵗ·LD²/2", px(T_MAX * 0.04), py(g0 * P.q ** (T_MAX * 0.04)) + 14);
    }
    const n = Math.min(t, T_MAX);
    for (const k of Object.keys(RULES)) {
      const H = runs[k].H;
      ctx.strokeStyle = RULES[k].color; ctx.lineWidth = 1.8; ctx.beginPath();
      for (let i = 0; i <= n; i++) (i ? ctx.lineTo : ctx.moveTo).call(ctx, px(i), py(H[i]));
      ctx.stroke();
    }
    let y = mt + 14;
    for (const k of Object.keys(RULES)) {
      ctx.fillStyle = RULES[k].color; ctx.fillRect(W - mr - 128, y - 8, 10, 10);
      ctx.fillStyle = fg(); ctx.fillText(RULES[k].name, W - mr - 114, y + 1); y += 15;
    }
  }

  function draw() {
    drawGeometry(); drawChart();
    const n = Math.min(t, T_MAX);
    stats.textContent = `t = ${n}   r = ${P.r.toFixed(3)}   q = ${P.q.toFixed(4)}   h_t: ` +
      Object.keys(RULES).map((k) => `${RULES[k].name} ${runs[k].H[n].toExponential(1)}`).join(" · ");
    verdict.textContent = P.r > 0
      ? `x* is interior (r = ${P.r.toFixed(2)}): Theorem 2.17 guarantees the factor q = ${P.q.toFixed(4)} per step for short steps and line search; the actual rate is usually much better. The open-loop rule does not converge linearly.`
      : P.R.name === "disk"
        ? "x* lies on the boundary (r = 0), so Theorem 2.17 does not apply. The disk is a strongly convex set and the gradient does not vanish at x*, which gives fast convergence for a different reason."
        : "x* lies on the boundary (r = 0), so Theorem 2.17 does not apply, and the short step slows down to a sublinear rate.";
  }

  function loop() {
    if (playing && t < T_MAX) { t = Math.min(T_MAX, t + 2); draw(); }
    raf = requestAnimationFrame(loop);
  }
  play.addEventListener("click", () => { playing = !playing; play.textContent = playing ? "pause" : "play"; if (playing && t >= T_MAX) t = 0; });
  restart.addEventListener("click", () => { t = 0; playing = true; play.textContent = "pause"; draw(); });
  let dragging = false;
  const moveTo = (ev) => {
    const r = geo.getBoundingClientRect();
    const u = ((ev.clientX - r.left) / r.width) * 2 * VIEW - VIEW, w = VIEW - ((ev.clientY - r.top) / r.height) * 2 * VIEW;
    model.set("cx", Math.round(clamp(u, -VIEW, VIEW) * 1000) / 1000);
    model.set("cy", Math.round(clamp(w, -VIEW, VIEW) * 1000) / 1000);
  };
  geo.addEventListener("pointerdown", (ev) => { dragging = true; geo.setPointerCapture(ev.pointerId); moveTo(ev); });
  geo.addEventListener("pointermove", (ev) => { if (dragging) moveTo(ev); });
  geo.addEventListener("pointerup", () => { dragging = false; });
  for (const key of ["region", "objective", "cx", "cy"]) model.on(`change:${key}`, start);
  start();
  loop();
  return () => cancelAnimationFrame(raf);
}

export default { render };
