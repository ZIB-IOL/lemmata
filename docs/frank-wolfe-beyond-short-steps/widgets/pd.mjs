// Frank–Wolfe step-size rules raced on one problem: f(x) = ½ (x − c)ᵀ Q (x − c) with
// Q = diag(1, μ), so L = 1, over a planar region. Every rule starts at the same point. The chart
// shows the computable primal-dual gap G_t of each rule on log–log axes, with the guarantee
// G_t ≤ 2LD²/(t + 2) of Proposition 4.1 dashed; the optional thin curves are the primal gaps
// f(x_{t+1}) − f(x*) ≤ G_t. Drag c. Everything runs in the browser (model.get/set/on only).

export const T_MAX = 2000;
const VIEW = 1.6; // the canvas shows [-VIEW, VIEW]²
const sgn = (v) => (v < 0 ? -1 : 1); // fixed tie-breaking: sgn(0) = +1
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
    path: (ctx, X, Y) => { ctx.rect(X(-1), Y(1), X(1) - X(-1), Y(-1) - Y(1)); },
  },
  disk: {
    name: "disk", diam: 2, start: [0, -1],
    lmo: (g) => { const n = Math.hypot(g[0], g[1]); return n === 0 ? [1, 0] : [-g[0] / n, -g[1] / n]; },
    inside: (p) => Math.hypot(p[0], p[1]) <= 1,
    path: (ctx, X, Y) => { ctx.arc(X(0), Y(0), X(1) - X(0), 0, 2 * Math.PI); },
  },
  triangle: {
    name: "triangle", diam: triDiam, start: TRI[1],
    lmo: (g) => TRI.reduce((b, p) => (dot(g, p) < dot(g, b) ? p : b), TRI[0]),
    inside: (p) => TRI.every((a, i) => {
      const b = TRI[(i + 1) % 3];
      return (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0]) >= 0;
    }),
    path: (ctx, X, Y) => { TRI.forEach((p, i) => (i ? ctx.lineTo : ctx.moveTo).call(ctx, X(p[0]), Y(p[1]))); ctx.closePath(); },
  },
};

export const RULES = {
  open: { name: "open loop", color: "#8a8a8a" },
  short: { name: "short step", color: "#3a86ff" },
  pd: { name: "primal-dual short step", color: "#d1495b" },
  ls: { name: "primal-dual line search", color: "#2a9d8f" },
  hb: { name: "heavy ball", color: "#e09f3e" },
};

// The problem: f, its gradient, the curvature d ↦ dᵀQd, and the exact minimum over the region.
export function problem(regionKey, mu, c) {
  const R = REGIONS[regionKey];
  const f = (x) => 0.5 * ((x[0] - c[0]) ** 2 + mu * (x[1] - c[1]) ** 2);
  const grad = (x) => [x[0] - c[0], mu * (x[1] - c[1])];
  const curv = (d) => d[0] * d[0] + mu * d[1] * d[1];
  let xs;
  if (R.inside(c)) xs = [c[0], c[1]];
  else if (regionKey === "square") xs = [clamp(c[0], -1, 1), clamp(c[1], -1, 1)];
  else if (regionKey === "disk") {
    // x_i = q_i c_i / (q_i + λ) with ‖x‖ = 1
    const at = (lam) => [c[0] / (1 + lam), (mu * c[1]) / (mu + lam)];
    let lo = 0, hi = 1;
    while (Math.hypot(...at(hi)) > 1) hi *= 2;
    for (let k = 0; k < 100; k++) { const m = (lo + hi) / 2; if (Math.hypot(...at(m)) > 1) lo = m; else hi = m; }
    xs = at(hi);
  } else {
    // minimum over the boundary: the best point on each edge
    let best = null;
    TRI.forEach((a, i) => {
      const b = TRI[(i + 1) % 3], d = sub(b, a);
      const s = clamp(-dot(grad(a), d) / curv(d), 0, 1), p = [a[0] + s * d[0], a[1] + s * d[1]];
      if (!best || f(p) < f(best)) best = p;
    });
    xs = best;
  }
  return { R, f, grad, curv, xs, fstar: f(xs), L: 1 };
}

// One run of a rule for T steps: iterates, primal-dual gaps G_t and primal gaps f(x_{t+1}) − f*.
export function simulate(P, ruleKey, T = T_MAX) {
  const { R, f, grad, curv, fstar, L } = P;
  const xs = [R.start.slice()], G = new Float64Array(T), H = new Float64Array(T);
  let x = R.start.slice(), low = 0, gbar = null, cst = 0, Gprev = Infinity;
  for (let t = 0; t < T; t++) {
    const g = grad(x);
    let v, gam;
    if (ruleKey === "hb") {
      gam = 2 / (t + 2);
      gbar = t === 0 ? g.slice() : [(1 - gam) * gbar[0] + gam * g[0], (1 - gam) * gbar[1] + gam * g[1]];
      cst = t === 0 ? f(x) - dot(g, x) : (1 - gam) * cst + gam * (f(x) - dot(g, x));
      v = R.lmo(gbar);
    } else {
      v = R.lmo(g);
      const d = sub(v, x), dd = dot(d, d), gap = -dot(g, d);
      const lowNew = f(x) - gap;
      if (ruleKey === "open") gam = 2 / (t + 2);
      else if (ruleKey === "short") gam = dd === 0 ? 0 : Math.min(1, gap / (L * dd));
      else if (t === 0) gam = 1;
      else if (ruleKey === "pd") gam = dd === 0 ? 1 : Math.min(1, Gprev / (L * dd));
      else { const q = curv(d); gam = q === 0 ? 1 : Math.min(1, Gprev / q); } // exact bound of a quadratic
      low = t === 0 ? lowNew : (1 - gam) * low + gam * lowNew;
    }
    x = [x[0] + gam * (v[0] - x[0]), x[1] + gam * (v[1] - x[1])];
    const lower = ruleKey === "hb" ? cst + dot(gbar, v) : low;
    G[t] = f(x) - lower; H[t] = f(x) - fstar; Gprev = G[t];
    xs.push(x);
  }
  return { xs, G, H };
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
  const box = el("div", "lemmata-pd");
  const controls = el("div", "pd-controls");
  const group = (label) => { const g = el("div", "pd-group"); g.append(el("span", "pd-label", label)); controls.append(g); return g; };
  const btns = {};
  const gRegion = group("Region");
  for (const k of Object.keys(REGIONS)) {
    const b = el("button", "pd-btn", REGIONS[k].name); b.type = "button";
    b.addEventListener("click", () => model.set("region", k)); gRegion.append(b); btns["region:" + k] = b;
  }
  const gObj = group("Objective");
  for (const [k, name] of [["round", "round (μ = 1)"], ["elongated", "elongated (μ = 0.15)"]]) {
    const b = el("button", "pd-btn", name); b.type = "button";
    b.addEventListener("click", () => model.set("objective", k)); gObj.append(b); btns["objective:" + k] = b;
  }
  const gRules = group("Rules");
  for (const k of Object.keys(RULES)) {
    const b = el("button", "pd-btn pd-rule", ""); b.type = "button";
    const sw = el("span", "pd-swatch"); sw.style.background = RULES[k].color;
    b.append(sw, document.createTextNode(RULES[k].name));
    b.addEventListener("click", () => {
      const on = new Set(rulesOn()); if (on.has(k)) on.delete(k); else on.add(k);
      model.set("rules", Object.keys(RULES).filter((r) => on.has(r)).join(","));
    });
    gRules.append(b); btns["rule:" + k] = b;
  }
  const gShow = group("Show");
  const primalBtn = el("button", "pd-btn", "primal gaps"); primalBtn.type = "button";
  primalBtn.addEventListener("click", () => model.set("primal", !model.get("primal")));
  const play = el("button", "pd-btn", "pause"); play.type = "button";
  const restart = el("button", "pd-btn", "restart"); restart.type = "button";
  gShow.append(primalBtn, play, restart);

  const panes = el("div", "pd-panes");
  const geo = el("canvas", "pd-geo"), chart = el("canvas", "pd-chart");
  panes.append(geo, chart);
  const stats = el("p", "pd-stats"), verdict = el("p", "pd-verdict");
  box.append(controls, panes, stats, verdict);
  root.append(box);
  const gctx = setupCanvas(geo, 300, 300), cctx = setupCanvas(chart, 370, 300);

  const rulesOn = () => String(model.get("rules") || "").split(",").filter((k) => RULES[k]);
  let P = null, runs = {}, t = 0, playing = true, raf = null;

  function start() {
    const region = REGIONS[model.get("region")] ? model.get("region") : "square";
    const mu = model.get("objective") === "round" ? 1 : 0.15;
    P = problem(region, mu, [model.get("cx"), model.get("cy")]);
    runs = {};
    for (const k of Object.keys(RULES)) runs[k] = simulate(P, k);
    t = 1;
    for (const [key, b] of Object.entries(btns)) {
      const [kind, k] = key.split(":");
      const on = kind === "region" ? k === region : kind === "objective" ? k === (mu === 1 ? "round" : "elongated") : rulesOn().includes(k);
      b.setAttribute("aria-pressed", on ? "true" : "false");
    }
    primalBtn.setAttribute("aria-pressed", model.get("primal") ? "true" : "false");
    draw();
  }

  const fg = () => getComputedStyle(root).color || "#333";
  const X = (u) => ((u + VIEW) / (2 * VIEW)) * 300, Y = (u) => ((VIEW - u) / (2 * VIEW)) * 300;

  function drawGeometry() {
    const ctx = gctx;
    ctx.clearRect(0, 0, 300, 300);
    ctx.beginPath(); P.R.path(ctx, X, Y);
    ctx.fillStyle = "rgba(136,136,136,0.16)"; ctx.fill();
    ctx.strokeStyle = "rgba(136,136,136,0.8)"; ctx.lineWidth = 1.2; ctx.stroke();
    for (const k of rulesOn()) {
      const xs = runs[k].xs, n = Math.min(t, xs.length - 1);
      ctx.beginPath(); ctx.strokeStyle = RULES[k].color; ctx.globalAlpha = 0.7; ctx.lineWidth = 1;
      for (let i = 0; i <= n; i++) (i ? ctx.lineTo : ctx.moveTo).call(ctx, X(xs[i][0]), Y(xs[i][1]));
      ctx.stroke(); ctx.globalAlpha = 1;
      ctx.beginPath(); ctx.fillStyle = RULES[k].color; ctx.arc(X(xs[n][0]), Y(xs[n][1]), 3.2, 0, 2 * Math.PI); ctx.fill();
    }
    const c = [model.get("cx"), model.get("cy")];
    ctx.strokeStyle = fg(); ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.moveTo(X(c[0]) - 5, Y(c[1]) - 5); ctx.lineTo(X(c[0]) + 5, Y(c[1]) + 5);
    ctx.moveTo(X(c[0]) - 5, Y(c[1]) + 5); ctx.lineTo(X(c[0]) + 5, Y(c[1]) - 5); ctx.stroke();
    ctx.fillStyle = fg(); ctx.font = "12px sans-serif"; ctx.fillText("c", X(c[0]) + 7, Y(c[1]) - 6);
    ctx.beginPath(); ctx.arc(X(P.xs[0]), Y(P.xs[1]), 4, 0, 2 * Math.PI); ctx.lineWidth = 1.2; ctx.stroke();
    ctx.fillText("x*", X(P.xs[0]) + 6, Y(P.xs[1]) + 14);
  }

  function drawChart() {
    const ctx = cctx, W = 370, Hh = 300, ml = 44, mr = 8, mt = 10, mb = 30;
    ctx.clearRect(0, 0, W, Hh);
    const guide = (s) => (2 * P.L * P.R.diam ** 2) / (s + 2);
    let lo = Infinity, hi = guide(1);
    for (const k of rulesOn()) for (let i = 0; i < T_MAX; i++) {
      const g = runs[k].G[i]; if (g > 0) { lo = Math.min(lo, g); hi = Math.max(hi, g); }
    }
    lo = Math.max(1e-10, Math.min(lo, guide(T_MAX)) / 2);
    const ly0 = Math.floor(Math.log10(lo)), ly1 = Math.ceil(Math.log10(hi));
    const px = (s) => ml + (Math.log10(s) / Math.log10(T_MAX)) * (W - ml - mr);
    const py = (g) => mt + ((ly1 - Math.log10(Math.max(g, 10 ** ly0))) / (ly1 - ly0)) * (Hh - mt - mb);
    ctx.strokeStyle = "rgba(136,136,136,0.35)"; ctx.fillStyle = fg(); ctx.font = "11px sans-serif"; ctx.lineWidth = 1;
    for (let e = ly0; e <= ly1; e++) {
      ctx.beginPath(); ctx.moveTo(ml, py(10 ** e)); ctx.lineTo(W - mr, py(10 ** e)); ctx.stroke();
      ctx.fillText("1e" + e, 4, py(10 ** e) + 4);
    }
    for (const s of [1, 10, 100, 1000]) {
      ctx.beginPath(); ctx.moveTo(px(s), mt); ctx.lineTo(px(s), Hh - mb); ctx.stroke();
      ctx.fillText(String(s), px(s) - 6, Hh - mb + 14);
    }
    ctx.fillText("t", W - mr - 8, Hh - 4);
    ctx.setLineDash([5, 4]); ctx.strokeStyle = fg(); ctx.globalAlpha = 0.6; ctx.beginPath();
    for (let s = 1; s <= T_MAX; s = Math.ceil(s * 1.05)) (s === 1 ? ctx.moveTo : ctx.lineTo).call(ctx, px(s), py(guide(s)));
    ctx.stroke(); ctx.setLineDash([]); ctx.globalAlpha = 1;
    ctx.fillText("2LD²/(t+2)", px(2), py(guide(2)) - 6);
    const n = Math.min(t, T_MAX - 1);
    for (const k of rulesOn()) {
      const curve = (arr, dash, width) => {
        ctx.setLineDash(dash); ctx.lineWidth = width; ctx.strokeStyle = RULES[k].color; ctx.beginPath();
        let first = true;
        for (let i = 1; i <= n; i = i < 60 ? i + 1 : Math.ceil(i * 1.02)) {
          if (!(arr[i] > 0)) { first = true; continue; }
          (first ? ctx.moveTo : ctx.lineTo).call(ctx, px(i), py(arr[i])); first = false;
        }
        ctx.stroke(); ctx.setLineDash([]);
      };
      curve(runs[k].G, [], 1.8);
      if (model.get("primal")) curve(runs[k].H, [2, 3], 1);
    }
  }

  function draw() {
    drawGeometry(); drawChart();
    const n = Math.min(t, T_MAX - 1), on = rulesOn();
    stats.textContent = `t = ${n}   G_t: ` + on.map((k) => `${RULES[k].name} ${runs[k].G[n].toExponential(1)}`).join(" · ");
    const best = on.slice().sort((a, b) => runs[a].G[n] - runs[b].G[n])[0];
    const over = on.filter((k) => runs[k].G.slice(1, n + 1).some((g, i) => g > (2 * P.L * P.R.diam ** 2) / (i + 3) + 1e-12));
    verdict.textContent = !on.length ? "Pick at least one rule." :
      `Smallest certified gap now: ${RULES[best].name}.` +
      (over.length ? ` Above the guarantee at some t: ${over.map((k) => RULES[k].name).join(", ")} (the guarantee covers open loop, the primal-dual rules and heavy ball, not the classical short step).` : " Every curve stays below the guarantee.");
  }

  function loop() {
    if (playing && t < T_MAX - 1) { t = Math.min(T_MAX - 1, t + Math.max(1, Math.floor(t / 45))); draw(); }
    raf = requestAnimationFrame(loop);
  }

  play.addEventListener("click", () => { playing = !playing; play.textContent = playing ? "pause" : "play"; if (playing && t >= T_MAX - 1) { t = 1; } });
  restart.addEventListener("click", () => { t = 1; playing = true; play.textContent = "pause"; draw(); });
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
  model.on("change:rules", () => start());
  model.on("change:primal", () => { primalBtn.setAttribute("aria-pressed", model.get("primal") ? "true" : "false"); draw(); });
  start();
  loop();
  return () => cancelAnimationFrame(raf);
}

export default { render };
