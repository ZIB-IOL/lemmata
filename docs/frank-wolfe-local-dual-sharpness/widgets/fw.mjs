// Frank–Wolfe on four planar regions, for f(x) = ½‖x − c‖² (so L = 1). Drag c, pick a region
// and a step-size rule, and watch the iterates, the atoms returned by the linear minimization
// oracle, and (t + 2)·F_t on log–log axes: a falling curve is F_t = o(1/t), a level one is the
// 1/t barrier. Everything runs in the browser; it uses only model.get/set/on (no kernel).

const T_MAX = 3000;
const VIEW = 1.75; // the canvas shows [-VIEW, VIEW]²
const sgn = (v) => (v < 0 ? -1 : 1); // a fixed tie-breaking rule: sgn(0) = +1
const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
const norm = (p) => Math.hypot(p[0], p[1]);

const A_ST = 0.55, R_ST = 0.6; // stadium: segment [-a, a] × {0} plus a disk of radius r

function projectL4(c) {
  // projection onto {x : x₁⁴ + x₂⁴ ≤ 1}: x_i + 4λx_i³ = c_i, with λ ≥ 0 found by bisection
  if (c[0] ** 4 + c[1] ** 4 <= 1) return [c[0], c[1]];
  const coord = (ci, lam) => {
    let lo = 0, hi = Math.abs(ci);
    for (let k = 0; k < 60; k++) {
      const u = (lo + hi) / 2;
      if (u + 4 * lam * u ** 3 > Math.abs(ci)) hi = u; else lo = u;
    }
    return sgn(ci) * (lo + hi) / 2;
  };
  let lo = 0, hi = 1;
  while (coord(c[0], hi) ** 4 + coord(c[1], hi) ** 4 > 1) hi *= 2;
  for (let k = 0; k < 60; k++) {
    const lam = (lo + hi) / 2;
    if (coord(c[0], lam) ** 4 + coord(c[1], lam) ** 4 > 1) lo = lam; else hi = lam;
  }
  return [coord(c[0], hi), coord(c[1], hi)];
}

// appended to the verdict on flat parts; filled in for the current step-size rule
let FLAT = "";

const REGIONS = {
  square: {
    name: "square", color: "#d1495b",
    lmo: (g) => [-sgn(g[0]), -sgn(g[1])],
    project: (c) => [clamp(c[0], -1, 1), clamp(c[1], -1, 1)],
    outline: () => [[-1, -1], [1, -1], [1, 1], [-1, 1]],
    verdict: (p) => (Math.abs(Math.abs(p[0]) - 1) < 1e-12 && Math.abs(Math.abs(p[1]) - 1) < 1e-12)
      ? "The minimizer is a corner. Once the oracle keeps returning it, the iterates reach it."
      : "The minimizer lies on a flat edge: local dual sharpness fails, and the oracle's answers " +
        "jump between the two corners." + FLAT,
  },
  disk: {
    name: "disk", color: "#2e86ab",
    lmo: (g) => { const n = norm(g); return n === 0 ? [1, 0] : [-g[0] / n, -g[1] / n]; },
    project: (c) => { const n = norm(c); return n <= 1 ? [c[0], c[1]] : [c[0] / n, c[1] / n]; },
    outline: () => Array.from({ length: 160 }, (_, k) => {
      const t = (2 * Math.PI * k) / 160; return [Math.cos(t), Math.sin(t)];
    }),
    verdict: () => "The disk is uniformly convex with q = 2 (strongly convex): local dual " +
      "sharpness holds around every minimizer.",
  },
  l4: {
    name: "ℓ₄ ball", color: "#3c9d5d",
    lmo: (g) => {
      const a = Math.abs(g[0]) ** (4 / 3) + Math.abs(g[1]) ** (4 / 3);
      if (a === 0) return [1, 0];
      const s = a ** 0.25;
      return [-sgn(g[0]) * Math.abs(g[0]) ** (1 / 3) / s, -sgn(g[1]) * Math.abs(g[1]) ** (1 / 3) / s];
    },
    project: projectL4,
    outline: () => Array.from({ length: 200 }, (_, k) => {
      const t = (2 * Math.PI * k) / 200, c = Math.cos(t), s = Math.sin(t);
      return [sgn(c) * Math.sqrt(Math.abs(c)), sgn(s) * Math.sqrt(Math.abs(s))];
    }),
    verdict: () => "The ℓ₄ ball is uniformly convex with q = 4, but not strongly convex: local " +
      "dual sharpness holds around every minimizer, with a weaker power.",
  },
  stadium: {
    name: "stadium", color: "#8e6fbf",
    lmo: (g) => {
      const n = norm(g), d = n === 0 ? [1, 0] : [g[0] / n, g[1] / n];
      return [-A_ST * sgn(g[0]) - R_ST * d[0], -R_ST * d[1]];
    },
    project: (c) => {
      const p = [clamp(c[0], -A_ST, A_ST), 0], d = [c[0] - p[0], c[1] - p[1]], n = norm(d);
      return n <= R_ST ? [c[0], c[1]] : [p[0] + (R_ST * d[0]) / n, p[1] + (R_ST * d[1]) / n];
    },
    outline: () => {
      const pts = [];
      for (let k = 0; k <= 60; k++) {
        const t = Math.PI / 2 - (Math.PI * k) / 60; pts.push([A_ST + R_ST * Math.cos(t), R_ST * Math.sin(t)]);
      }
      for (let k = 0; k <= 60; k++) {
        const t = -Math.PI / 2 - (Math.PI * k) / 60; pts.push([-A_ST + R_ST * Math.cos(t), R_ST * Math.sin(t)]);
      }
      return pts;
    },
    verdict: (p) => Math.abs(p[0]) < A_ST - 1e-9
      ? "The minimizer lies on a flat side of the stadium: local dual sharpness fails there, " +
        "and the oracle's answers jump between the ends of the side." + FLAT
      : "The minimizer lies on a round cap: local dual sharpness holds there, although the " +
        "stadium is not uniformly convex.",
  },
};

const RULES = {
  short: { name: "short step", gamma: (x, v, c) => {
    const d = [v[0] - x[0], v[1] - x[1]], dd = d[0] * d[0] + d[1] * d[1];
    if (dd === 0) return 0;
    const gap = (x[0] - c[0]) * (x[0] - v[0]) + (x[1] - c[1]) * (x[1] - v[1]);
    return clamp(gap / dd, 0, 1);
  } },
  open: { name: "open loop 2/(t+2)", gamma: (_x, _v, _c, t) => 2 / (t + 2) },
};

function el(tag, cls, text) {
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

function render({ model, el: root }) {
  const box = el("div", "lemmata-fw");
  const controls = el("div", "fw-controls");
  const regionRow = el("div", "fw-group"), ruleRow = el("div", "fw-group"), runRow = el("div", "fw-group");
  regionRow.append(el("span", "fw-label", "Region"));
  ruleRow.append(el("span", "fw-label", "Step size"));
  const buttons = {};
  for (const [k, r] of Object.entries(REGIONS)) {
    const b = el("button", "fw-btn", r.name); b.type = "button";
    b.addEventListener("click", () => model.set("region", k));
    buttons[k] = b; regionRow.append(b);
  }
  for (const [k, r] of Object.entries(RULES)) {
    const b = el("button", "fw-btn", r.name); b.type = "button";
    b.addEventListener("click", () => model.set("rule", k));
    buttons["rule:" + k] = b; ruleRow.append(b);
  }
  const play = el("button", "fw-btn fw-play", "Pause"); play.type = "button";
  const restart = el("button", "fw-btn", "Restart"); restart.type = "button";
  const speed = el("input"); speed.type = "range"; speed.min = "0"; speed.max = "4"; speed.value = "2";
  speed.setAttribute("aria-label", "Speed");
  runRow.append(play, restart, el("span", "fw-label", "speed"), speed);
  controls.append(regionRow, ruleRow, runRow);

  const panes = el("div", "fw-panes");
  const geo = el("canvas", "fw-geo"), chart = el("canvas", "fw-chart");
  geo.setAttribute("role", "img");
  geo.setAttribute("aria-label", "Feasible region, iterates and oracle atoms; drag to move the target c");
  chart.setAttribute("role", "img");
  chart.setAttribute("aria-label", "(t+2) times the primal gap against t, on logarithmic axes");
  panes.append(geo, chart);
  const stats = el("p", "fw-stats"), verdict = el("p", "fw-verdict");
  box.append(controls, panes, stats, verdict);
  root.append(box);

  const W = 300, H = 300, CW = 370, CH = 300;
  const g = setupCanvas(geo, W, H), k = setupCanvas(chart, CW, CH);
  const toPx = (p) => [((p[0] + VIEW) / (2 * VIEW)) * W, ((VIEW - p[1]) / (2 * VIEW)) * H];
  const toWorld = (px, py) => [(px / W) * 2 * VIEW - VIEW, VIEW - (py / H) * 2 * VIEW];
  const ink = () => getComputedStyle(box).color || "#333";

  let state = null, ghost = null, running = true, raf = 0;
  const reduced = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  function start() {
    const region = REGIONS[model.get("region")] || REGIONS.square;
    const rule = RULES[model.get("rule")] || RULES.short;
    const c = [model.get("cx"), model.get("cy")];
    if (state && state.ys.length > 50) ghost = { ys: state.ys, label: `${state.region.name}, ${state.rule.name}` };
    const xstar = region.project(c);
    const fstar = 0.5 * ((xstar[0] - c[0]) ** 2 + (xstar[1] - c[1]) ** 2);
    const x0 = [-0.45, -0.35]; // an interior point of all four regions
    state = { region, rule, c, xstar, fstar, xs: [x0], vs: [], ys: [] };
    for (const [kk, b] of Object.entries(buttons)) {
      const on = kk === model.get("region") || kk === "rule:" + model.get("rule");
      b.setAttribute("aria-pressed", String(on));
    }
    FLAT = model.get("rule") === "open"
      ? " Open-loop steps behave differently on flat parts; see the text below."
      : " With short steps (t+2)·F_t levels off: the 1/t barrier.";
    verdict.textContent = norm([c[0] - xstar[0], c[1] - xstar[1]]) < 1e-12
      ? "The target c lies inside the region, so the minimizer is c itself, an interior point " +
        "with ∇f = 0. Local dual sharpness holds there: the gap is at least ‖g‖ times the " +
        "distance to the boundary."
      : region.verdict(xstar);
    running = !reduced; play.textContent = running ? "Pause" : "Play";
    if (reduced) advance(T_MAX);
    draw();
    loop();
  }

  function advance(n) {
    const s = state;
    for (let j = 0; j < n && s.ys.length < T_MAX; j++) {
      const t = s.ys.length, x = s.xs[s.xs.length - 1];
      const grad = [x[0] - s.c[0], x[1] - s.c[1]];
      const v = s.region.lmo(grad);
      const fx = 0.5 * (grad[0] ** 2 + grad[1] ** 2);
      s.ys.push(Math.max(0, fx - s.fstar) * (t + 2));
      const gam = s.rule.gamma(x, v, s.c, t);
      s.vs.push(v);
      s.xs.push([x[0] + gam * (v[0] - x[0]), x[1] + gam * (v[1] - x[1])]);
    }
  }

  function drawGeometry() {
    const s = state, col = ink();
    g.clearRect(0, 0, W, H);
    // level sets of f
    g.strokeStyle = col; g.globalAlpha = 0.12; g.lineWidth = 1;
    const cpx = toPx(s.c);
    for (let r = 0.25; r < 2 * VIEW * 1.5; r += 0.25) {
      g.beginPath(); g.arc(cpx[0], cpx[1], (r / (2 * VIEW)) * W, 0, 2 * Math.PI); g.stroke();
    }
    g.globalAlpha = 1;
    // the region
    const out = s.region.outline().map(toPx);
    g.beginPath(); out.forEach((p, i) => (i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]))); g.closePath();
    g.fillStyle = s.region.color + "22"; g.fill();
    g.strokeStyle = s.region.color; g.lineWidth = 2; g.stroke();
    // trail of iterates
    const n = s.xs.length;
    g.strokeStyle = col; g.globalAlpha = 0.55; g.lineWidth = 1.2; g.beginPath();
    for (let i = Math.max(0, n - 400); i < n; i++) {
      const p = toPx(s.xs[i]); i === Math.max(0, n - 400) ? g.moveTo(p[0], p[1]) : g.lineTo(p[0], p[1]);
    }
    g.stroke(); g.globalAlpha = 1;
    // recent oracle atoms, fading
    for (let i = Math.max(0, s.vs.length - 12); i < s.vs.length; i++) {
      const p = toPx(s.vs[i]), a = (i - (s.vs.length - 12)) / 12;
      g.fillStyle = s.region.color; g.globalAlpha = 0.15 + 0.85 * a;
      g.fillRect(p[0] - 4, p[1] - 4, 8, 8);
    }
    g.globalAlpha = 1;
    // current step: x_t → v_t
    if (s.vs.length) {
      const x = toPx(s.xs[n - 2] || s.xs[0]), v = toPx(s.vs[s.vs.length - 1]);
      g.setLineDash([4, 3]); g.strokeStyle = s.region.color; g.lineWidth = 1.5;
      g.beginPath(); g.moveTo(x[0], x[1]); g.lineTo(v[0], v[1]); g.stroke(); g.setLineDash([]);
    }
    const xt = toPx(s.xs[n - 1]);
    g.fillStyle = col; g.beginPath(); g.arc(xt[0], xt[1], 4, 0, 2 * Math.PI); g.fill();
    // minimizer and target
    const xs = toPx(s.xstar);
    g.strokeStyle = col; g.lineWidth = 1.5; g.beginPath(); g.arc(xs[0], xs[1], 6, 0, 2 * Math.PI); g.stroke();
    g.fillStyle = col; g.font = "13px sans-serif"; g.fillText("x⋆", xs[0] + 8, xs[1] - 6);
    g.strokeStyle = "#e07a1f"; g.lineWidth = 2;
    g.beginPath(); g.arc(cpx[0], cpx[1], 7, 0, 2 * Math.PI); g.stroke();
    g.beginPath(); g.moveTo(cpx[0] - 11, cpx[1]); g.lineTo(cpx[0] + 11, cpx[1]);
    g.moveTo(cpx[0], cpx[1] - 11); g.lineTo(cpx[0], cpx[1] + 11); g.stroke();
    g.fillStyle = "#e07a1f"; g.fillText("c", cpx[0] + 10, cpx[1] + 16);
  }

  function drawChart() {
    const s = state, col = ink();
    const L = 46, R = 10, Tp = 12, B = 34, pw = CW - L - R, ph = CH - Tp - B;
    k.clearRect(0, 0, CW, CH);
    const lx = (t) => L + (Math.log10(t + 1) / Math.log10(T_MAX)) * pw;
    const all = s.ys.concat(ghost ? ghost.ys : []).filter((y) => y > 0);
    const ymax = Math.max(1, Math.ceil(Math.log10(Math.max(...all.slice(0, 50), 1e-12)) + 0.3));
    const ymin = -8;
    const ly = (y) => Tp + ((ymax - Math.log10(Math.max(y, 10 ** ymin))) / (ymax - ymin)) * ph;
    k.strokeStyle = col; k.fillStyle = col; k.font = "11px sans-serif"; k.lineWidth = 1;
    for (let e = ymin; e <= ymax; e += 2) {
      const y = ly(10 ** e); k.globalAlpha = 0.15; k.beginPath(); k.moveTo(L, y); k.lineTo(L + pw, y); k.stroke();
      k.globalAlpha = 0.8; k.fillText(`1e${e}`, 4, y + 4);
    }
    for (const t of [1, 10, 100, 1000]) {
      const x = lx(t - 1); k.globalAlpha = 0.15; k.beginPath(); k.moveTo(x, Tp); k.lineTo(x, Tp + ph); k.stroke();
      k.globalAlpha = 0.8; k.fillText(String(t), x - 6, Tp + ph + 14);
    }
    k.globalAlpha = 0.9; k.fillText("t", L + pw - 8, Tp + ph + 28);
    k.fillText("(t+2)·F_t", L + 6, Tp + 12);
    const curve = (ys, color, width, alpha) => {
      k.strokeStyle = color; k.lineWidth = width; k.globalAlpha = alpha; k.beginPath();
      ys.forEach((y, t) => { const X = lx(t), Y = ly(y); t ? k.lineTo(X, Y) : k.moveTo(X, Y); });
      k.stroke(); k.globalAlpha = 1;
    };
    if (ghost) {
      curve(ghost.ys, col, 1.2, 0.3);
      k.globalAlpha = 0.5; k.fillStyle = col; k.fillText(`previous: ${ghost.label}`, L + 6, Tp + ph - 8);
      k.globalAlpha = 1;
    }
    curve(s.ys, s.region.color, 2, 1);
  }

  function draw() {
    drawGeometry(); drawChart();
    const s = state, t = s.ys.length;
    const F = t ? s.ys[t - 1] / (t + 1) : NaN;
    const x = s.xs[t - 1], v = s.vs[t - 1];
    stats.textContent = t
      ? `t = ${t - 1}   F_t = ${F.toExponential(2)}   (t+2)·F_t = ${s.ys[t - 1].toExponential(2)}` +
        `   ‖s_t − x_t‖ = ${norm([v[0] - x[0], v[1] - x[1]]).toExponential(1)}`
      : "";
  }

  function loop() {
    cancelAnimationFrame(raf);
    const tick = () => {
      if (!running || state.ys.length >= T_MAX) { draw(); return; }
      advance([1, 2, 6, 20, 60][Number(speed.value)]);
      draw();
      raf = requestAnimationFrame(tick);
    };
    raf = requestAnimationFrame(tick);
  }

  play.addEventListener("click", () => {
    running = !running; play.textContent = running ? "Pause" : "Play";
    if (running) loop();
  });
  restart.addEventListener("click", () => { ghost = null; state = null; start(); });

  let dragging = false;
  const moveTo = (ev) => {
    const r = geo.getBoundingClientRect();
    const p = toWorld(((ev.clientX - r.left) / r.width) * W, ((ev.clientY - r.top) / r.height) * H);
    model.set("cx", Math.round(clamp(p[0], -VIEW, VIEW) * 1000) / 1000);
    model.set("cy", Math.round(clamp(p[1], -VIEW, VIEW) * 1000) / 1000);
  };
  geo.addEventListener("pointerdown", (ev) => { dragging = true; geo.setPointerCapture(ev.pointerId); moveTo(ev); });
  geo.addEventListener("pointermove", (ev) => { if (dragging) moveTo(ev); });
  geo.addEventListener("pointerup", () => { dragging = false; });

  for (const key of ["region", "rule", "cx", "cy"]) model.on(`change:${key}`, start);
  start();
  return () => cancelAnimationFrame(raf);
}

export default { render };
