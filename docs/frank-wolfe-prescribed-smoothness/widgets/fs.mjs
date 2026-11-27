// Three examples of the entry, computed in the browser (the widget uses only model.get/set/on).
//  - planar: smooth planar bodies K + B_r (K a point, a segment, a triangle or an ellipse) and
//    f(x) = ½‖x − c‖²; drag c. Frank–Wolfe with the LMO of the body, Frank–Wolfe on the inner
//    parallel body K (the upper bound for isotropic quadratics), and projected gradient with
//    Frank–Wolfe projections (the linear rate with inner and outer tangent balls).
//  - hard: an instance of the hard bodies C_I in dimension 256k + 1, with the vertex LMO, an LMO
//    that answers the vertical direction with the barycenter of the bottom face, or the LMO of a
//    body with perturbed vertices.
//  - hilbert: the fixed body in a Hilbert space with f(v, x) = ((v + 4)² + ‖x‖²)/2, simulated
//    exactly on the coordinates in use: Frank–Wolfe from the exposed start (open loop and exact
//    line search) between the two bounds, and a single call in the vertical direction.

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

/** Primal gaps after t oracle calls, t = 0..T, for the three methods on K + B_r, target c. */
export function simulatePlanar(coreKey, c, T) {
  const K = CORES[coreKey], r = R_BALL;
  const lmoC = (q) => { const n = norm(q); return n === 0 ? add(K.lmo([0, 1]), [0, -r])
    : sub(K.lmo(q), mul(q, r / n)); };
  const pk = K.proj(c), dist = Math.max(0, norm(sub(c, pk)) - r), fstar = 0.5 * dist * dist;
  const gap = (x) => Math.max(0, 0.5 * dot(sub(x, c), sub(x, c)) - fstar);
  const lift = (a) => add(a, clip(sub(c, a), r));
  const e = [0, 1];
  // Frank–Wolfe with short steps, started at the body's answer for e
  const fw = [], fwPath = [];
  let x = lmoC(e);
  fw.push(gap(x)); fwPath.push(x);
  for (let t = 1; t <= T; t++) {
    const g = sub(x, c), v = lmoC(g), d = sub(x, v), dd = dot(d, d);
    const gam = dd > 0 ? Math.min(1, Math.max(0, dot(g, d) / dd)) : 0;
    x = sub(x, mul(d, gam)); fw.push(gap(x)); fwPath.push(x);
  }
  // Frank–Wolfe on K: one call for a point of K, then steps 2/(j+2) on K, plus the ball part
  const qm = [], qmPath = [];
  let a = add(lmoC(e), mul(e, r));
  qm.push(gap(lift(a))); qmPath.push(lift(a));
  for (let j = 0; j < T; j++) {
    const g = sub(lift(a), c);
    const s = norm(g) === 0 ? a : K.lmo(g);
    a = add(mul(a, 1 - 2 / (j + 2)), mul(s, 2 / (j + 2)));
    qm.push(gap(lift(a))); qmPath.push(lift(a));
  }
  // projected gradient with Frank–Wolfe projections: exact line search on K for ½‖a − c‖²
  const jm = [], jmPath = [], jmCalls = [];
  const x0 = lmoC(e), q0 = sub(x0, c);
  a = norm(q0) === 0 ? x0 : add(lmoC(q0), mul(q0, r / norm(q0)));
  const first = norm(q0) === 0 ? x0 : lmoC(q0);
  let used = norm(q0) === 0 ? 1 : 2;
  jm.push(gap(first)); jmPath.push(first); jmCalls.push(used);
  for (let t = 1; t <= T; t++) {
    const q = sub(a, c);
    if (norm(q) > r) {
      const s = K.lmo(q), G = dot(q, sub(a, s)), H = dot(sub(s, a), sub(s, a));
      const lam = H > 0 ? Math.min(1, Math.max(0, G / H)) : 1;
      a = add(a, mul(sub(s, a), lam)); used++;
    }
    jm.push(gap(lift(a))); jmPath.push(lift(a)); jmCalls.push(used);
  }
  const D = K.diam + 2 * r;
  let rate = null;
  if (K.outer !== undefined) {
    const R = r + K.outer, cc = R === r ? 1 : 0.5 * Math.min(1, r / (2 * (R - r)));
    rate = (t) => (1 - cc) ** t * D * D / 2;
  }
  const calls = { fw: fw.map((_, t) => t + 1), qm: qm.map((_, j) => j + 1), jm: jmCalls };
  return { fw, qm, jm, fwPath, qmPath, jmPath, calls, delta: K.diam, D, rate, xstar: lift(pk), lmoC };
}

function mulberry(seed) {
  return () => {
    seed |= 0; seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function projSimplex(v) {
  const u = [...v].sort((p, q) => q - p);
  let css = 0, th = 0;
  for (let i = 0; i < u.length; i++) {
    css += u[i]; const t = (css - 1) / (i + 1); if (u[i] - t > 0) th = t;
  }
  return v.map((x) => Math.max(0, x - th));
}

/** The hard bodies with a = r = 1 (zero-based indices; index 0 is the index 1 of the text):
 * primal gaps after t calls for Frank–Wolfe, Frank–Wolfe on K and a method that reads I off the
 * answer, with the vertex LMO, the barycenter answer or the LMO of a body with perturbed vertices.
 * `found[t]` lists the indices of I that appear in the t-th answer to Frank–Wolfe on K. */
export function simulateHard(k, rule, T, seed = 7) {
  const N = 256 * k, d = 8 * k, rnd = mulberry(seed);
  const indexSet = [0], pool = Array.from({ length: N - 1 }, (_, i) => i + 1);
  for (let i = 0; i < d - 1; i++) indexSet.push(pool.splice(Math.floor(rnd() * pool.length), 1)[0]);
  indexSet.sort((p, q) => p - q);
  const xi = indexSet.map(() => 0.02 * (2 * rnd() - 1));
  const zeta = indexSet.map(() => 0.02 * (2 * rnd() - 1));
  const s = 1e-6; // thickening; small enough that early answers have one index of positive weight
  // returns [horizontal part, height, indices of I with positive weight]
  const oracle = (qx, qy) => {
    const nq = Math.hypot(qy, Math.hypot(...qx));
    const x = new Float64Array(N);
    if (nq === 0) { x[0] = 1; return [x, 0, []]; }
    if (rule === "unique") {
      const g = indexSet.map((j, m) => (qx[j] * (1 + xi[m]) + qy * (1 + zeta[m])) / nq);
      const u = projSimplex(g.map((v) => -v / (2 * s)));
      let hy = 0, uu = 0; const hit = [];
      indexSet.forEach((j, m) => {
        x[j] += u[m] * (1 + xi[m]); hy += u[m] * (1 + zeta[m]); uu += u[m] * u[m];
        if (u[m] > 0) hit.push(j);
      });
      const rad = s * (1 - uu) + 1;
      for (let i = 0; i < N; i++) x[i] -= rad * qx[i] / nq;
      return [x, hy - rad * qy / nq, hit];
    }
    let mn = Infinity;
    for (const j of indexSet) mn = Math.min(mn, qx[j]);
    const J = rule === "barycenter" ? indexSet.filter((j) => qx[j] === mn)
      : [indexSet.find((j) => qx[j] === mn)];
    for (const j of J) x[j] += 1 / J.length;
    for (let i = 0; i < N; i++) x[i] -= qx[i] / nq;
    return [x, 1 - qy / nq, J];
  };
  let H = Math.sqrt(1 / d + 33 * 33);
  if (rule === "unique") {
    // distance from c = (0, -32) to the perturbed inner body: minimize the convex function
    // ‖Σ u_m v_m − c‖ − s (1 − ‖u‖²) over the simplex, by projected gradient with backtracking
    const phi = (u) => {
      let q = 0, h = 32, uu = 0;
      indexSet.forEach((_, m) => { q += (u[m] * (1 + xi[m])) ** 2; h += u[m] * (1 + zeta[m]); uu += u[m] ** 2; });
      return [Math.sqrt(q + h * h) - s * (1 - uu), Math.sqrt(q + h * h), h];
    };
    let u = indexSet.map(() => 1 / d), [val] = phi(u), step = 30;
    for (let it = 0; it < 5000; it++) {
      const [, nrm, h] = phi(u);
      const grad = indexSet.map((_, m) => (u[m] * (1 + xi[m]) ** 2 + h * (1 + zeta[m])) / nrm + 2 * s * u[m]);
      let moved = false;
      while (step > 1e-9) {
        const v = projSimplex(u.map((x, m) => x - step * grad[m]));
        const [fv] = phi(v); let dd = 0; v.forEach((x, m) => { dd += (x - u[m]) ** 2; });
        if (fv <= val - dd / (2 * step)) { moved = dd > 0 && val - fv > 1e-17; u = v; val = fv; step *= 1.5; break; }
        step /= 2;
      }
      if (!moved) break;
    }
    H = val;
  }
  const fstar = 0.5 * (H - 1) ** 2 - 0.5 * 32 * 32;
  const f = (x, y) => { let q = y * y; for (let i = 0; i < N; i++) q += x[i] * x[i]; return 0.5 * q + 32 * y; };
  const gap = (x, y) => Math.max(0, f(x, y) - fstar);
  // Frank–Wolfe with short steps from the start point (e_1, 0)
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
  // Frank–Wolfe on K; the first call is the vertical direction
  const center = [new Float64Array(N), -32];
  const lift = (ax, ay) => {
    const dx = ax.map((v) => -v), dy = center[1] - ay, n = Math.hypot(dy, Math.hypot(...dx));
    const sc = n <= 1 ? 1 : 1 / n;
    return [ax.map((v, i) => v + sc * dx[i]), ay + sc * dy];
  };
  const qm = [], probe = [], found = [[0]];
  let [ax, ay, hit0] = oracle(new Float64Array(N), 1); ay += 1;
  const revealed = rule === "barycenter";
  let [lx, ly] = lift(ax, ay);
  qm.push(gap(lx, ly)); probe.push(gap(lx, ly)); found.push(hit0);
  for (let j = 0; j < T; j++) {
    const gx = lx, gy = ly + 32;
    const [vx, vy0, hit] = oracle(gx, gy);
    let vy = vy0;
    const ng = Math.hypot(gy, Math.hypot(...gx));
    if (ng > 0) { for (let i = 0; i < N; i++) vx[i] += gx[i] / ng; vy += gy / ng; }
    const gam = 2 / (j + 2);
    ax = ax.map((v, i) => (1 - gam) * v + gam * vx[i]); ay = (1 - gam) * ay + gam * vy;
    [lx, ly] = lift(ax, ay);
    qm.push(gap(lx, ly)); probe.push(revealed ? 0 : gap(lx, ly));
    if (j + 2 <= T) found.push(hit);
  }
  const calls = { fw: fw.map((_, t) => t), qm: qm.map((_, j) => j + 1) };
  return { fw, qm, probe, found, calls, indexSet, k, d, N, lower: 1 / (16 * k), delta: Math.SQRT2 };
}

/** The fixed Hilbert-space body (zero-based indices): w_i = 2^{-i}/64, Gram matrix
 * B_ij = [i = j] - w_max(i,j), f(v, x) = ((v + 4)² + ‖x‖²)/2 with minimizer z⋆ = (-1, 0).
 * A point is (v, x) with x the coordinates of its horizontal part Σ x_i d_i. Each answer uses at
 * most one new coordinate, so T + margin coordinates make the simulation exact. Runs Frank–Wolfe
 * from the exposed start with step sizes 2/(t+2) ("open") and with exact line search ("line"). */
export function simulateHilbert(T, margin = 40) {
  const n = T + margin, w = new Float64Array(n), w2 = new Float64Array(n);
  for (let i = 0; i < n; i++) { w[i] = 2 ** -i / 64; w2[i] = w[i] * w[i]; }
  const Bx = (x) => { // (Bx)_i = x_i - w_i Σ_{j≤i} x_j - Σ_{j>i} w_j x_j
    const out = new Float64Array(n), suf = new Float64Array(n + 1);
    for (let i = n - 1; i >= 0; i--) suf[i] = suf[i + 1] + w[i] * x[i];
    let pre = 0;
    for (let i = 0; i < n; i++) { pre += x[i]; out[i] = x[i] - (w[i] * pre + suf[i + 1]); }
    return out;
  };
  const dotB = (x, y) => { const b = Bx(y); let s = 0; for (let i = 0; i < n; i++) s += x[i] * b[i]; return s; };
  // LMO for the direction (G, Σ x_i d_i): the parameter u of the answer maximizes
  // Σ α_i u_i − β_i u_i² over u ≥ 0, Σ u_i ≤ 1; the answer is c(u) − r(u) q/‖q‖.
  const lmo = (G, x) => {
    const bx = Bx(x);
    let q2 = G * G; for (let i = 0; i < n; i++) q2 += x[i] * bx[i];
    const Q = Math.sqrt(q2);
    const alpha = new Float64Array(n), beta = new Float64Array(n), u = new Float64Array(n);
    for (let i = 0; i < n; i++) { beta[i] = Q * w2[i] / 100; alpha[i] = -bx[i] - G * w2[i] + beta[i]; }
    let free = 0; for (let i = 0; i < n; i++) if (alpha[i] > 0) free += alpha[i] / (2 * beta[i]);
    if (free <= 1) { for (let i = 0; i < n; i++) if (alpha[i] > 0) u[i] = alpha[i] / (2 * beta[i]); }
    else { // the mass constraint is active: water-filling, written relative to the largest α
      const ord = [...Array(n).keys()].filter((i) => alpha[i] > 0).sort((p, q) => alpha[q] - alpha[p]);
      const top = alpha[ord[0]];
      let num = 1, den = 0, last = 0, delta = 0;
      for (last = 0; last < ord.length; last++) {
        const i = ord[last];
        num += (top - alpha[i]) / (2 * beta[i]); den += 1 / (2 * beta[i]); delta = num / den;
        if (last + 1 === ord.length || top - delta >= alpha[ord[last + 1]]) break;
      }
      for (let m = 0; m <= last; m++) {
        const i = ord[m]; u[i] = Math.max(0, (delta - (top - alpha[i])) / (2 * beta[i]));
      }
    }
    let a = 0, rad = 1;
    for (let i = 0; i < n; i++) { a += w2[i] * u[i]; rad += w2[i] * (u[i] - u[i] * u[i]) / 100; }
    const y = new Float64Array(n);
    for (let i = 0; i < n; i++) y[i] = u[i] - (rad / Q) * x[i];
    return [a - rad * G / Q, y];
  };
  const f = (v, x) => ((v + 4) ** 2 + dotB(x, x)) / 2, fstar = 4.5;
  const q0 = new Float64Array(n); q0[0] = -1 / 8; // the start is the minimizer for -(−1, d_0/8)
  const [sv, sx] = lmo(1, q0);
  const runs = {};
  for (const rule of ["open", "line"]) {
    let v = sv; const x = Float64Array.from(sx);
    const gap = [f(v, x) - fstar], charts = [Float64Array.from(x)];
    for (let t = 0; t < T; t++) {
      const [yv, yx] = lmo(v + 4, x);
      let gam = 2 / (t + 2);
      if (rule === "line") {
        const dv = v - yv, dx = x.map((xi, i) => xi - yx[i]);
        const num = (v + 4) * dv + dotB(x, dx), den = dv * dv + dotB(dx, dx);
        gam = den > 0 ? Math.min(1, Math.max(0, num / den)) : 0;
      }
      v += gam * (yv - v);
      for (let i = 0; i < n; i++) x[i] += gam * (yx[i] - x[i]);
      gap.push(Math.max(0, f(v, x) - fstar)); charts.push(Float64Array.from(x));
    }
    runs[rule] = { gap, charts };
  }
  const [zv, zx] = lmo(1, new Float64Array(n)); // one call in the vertical direction
  const vertical = [f(sv, sx) - fstar];
  for (let t = 1; t <= T; t++) vertical.push(Math.max(0, f(zv, zx) - fstar));
  return {
    open: runs.open.gap, line: runs.line.gap, charts: runs.open.charts, vertical,
    lower: (t) => 31 / (256 * (t + 1)), upper: (t) => 2 * (15 / 4) ** 2 / (t + 2),
  };
}

/** The smallest primal gap among the points computed with at most s oracle calls, s = 0..T
 * (NaN before the first point). `vals[i]` is computed with `calls[i]` calls. */
export function byCalls(vals, calls, T) {
  const out = new Array(T + 1).fill(NaN); let best = Infinity, i = 0;
  for (let s = 0; s <= T; s++) {
    while (i < vals.length && calls[i] <= s) { best = Math.min(best, vals[i]); i++; }
    if (best < Infinity) out[s] = best;
  }
  return out;
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
const COLORS = { a: "#d1495b", b: "#2e86ab", c: "#3c9d5d", d: "#e07a1f" };
// values below 1e-12 are rounding, except for curves that are exact by construction
const fmt = (y, exact) => (exact && y === 0 ? "0" : y < 1e-12 ? "< 1e−12" : y.toExponential(1).replace("-", "−"));
const PLANAR = Object.keys(CORES);
const HORIZON = { planar: 1000, hard: 300, hilbert: 300 };

function render({ model, el: root }) {
  const box = elt("div", "lemmata-fs");
  const buttons = [];
  const button = (row, label, pressed, act) => {
    const b = elt("button", "fs-btn", label); b.type = "button";
    b.addEventListener("click", act); buttons.push([b, pressed]); row.append(b);
  };
  const group = (label) => { const g = elt("div", "fs-group"); g.append(elt("span", "fs-label", label)); return g; };
  const modeOf = () => { const b = model.get("body") || "segment"; return PLANAR.includes(b) ? "planar" : b; };
  let lastPlanar = PLANAR.includes(model.get("body")) ? model.get("body") : "segment";

  const rowEx = group("Example");
  button(rowEx, "smooth planar body", () => modeOf() === "planar", () => model.set("body", lastPlanar));
  button(rowEx, "hard body", () => modeOf() === "hard", () => model.set("body", "hard"));
  button(rowEx, "fixed Hilbert body", () => modeOf() === "hilbert", () => model.set("body", "hilbert"));
  const rowBody = group("Body");
  for (const key of PLANAR) {
    button(rowBody, CORES[key].name, () => model.get("body") === key,
      () => { lastPlanar = key; model.set("body", key); });
  }
  const rowK = group("Dimension");
  for (const kk of [1, 2, 4, 8]) {
    button(rowK, `256·${kk} + 1`, () => Number(model.get("k") || 2) === kk, () => model.set("k", kk));
  }
  const rowLMO = group("LMO");
  for (const [key, lab] of [["vertex", "vertex LMO"], ["barycenter", "barycenter answer"],
    ["unique", "perturbed vertices"]]) {
    button(rowLMO, lab, () => (model.get("rule") || "vertex") === key, () => model.set("rule", key));
  }
  const rowT = group("Oracle calls");
  const slider = elt("input", "fs-slider"); slider.type = "range"; slider.min = "0"; slider.max = "100";
  slider.step = "1"; slider.setAttribute("aria-label", "Number of oracle calls");
  const tOut = elt("span", "fs-t");
  slider.addEventListener("input", () => model.set("t", Number(slider.value)));
  rowT.append(slider, tOut);

  const panes = elt("div", "fs-panes");
  const geo = elt("canvas", "fs-geo"), chartBox = elt("div", "fs-chartbox"), chart = elt("canvas", "fs-chart");
  const legend = elt("ul", "fs-legend");
  geo.setAttribute("role", "img"); chart.setAttribute("role", "img");
  chart.setAttribute("aria-label", "Smallest primal gap so far against the number of oracle calls, logarithmic axes");
  chartBox.append(chart, legend);
  panes.append(geo, chartBox);
  const caption = elt("p", "fs-caption");
  box.append(rowEx, rowBody, rowK, rowLMO, rowT, panes, caption);
  root.append(box);

  const W = 300, H = 300, CW = 380, CH = 280, VIEW = 1.9;
  const g = setupCanvas(geo, W, H), k = setupCanvas(chart, CW, CH);
  const toPx = (p) => [((p[0] + VIEW) / (2 * VIEW)) * W, ((VIEW - p[1]) / (2 * VIEW)) * H];
  const ink = () => getComputedStyle(box).color || "#333";
  const font = (px) => `${px}px ${getComputedStyle(box).fontFamily || "sans-serif"}`;
  const cache = new Map();
  const memo = (key, fn) => { if (!cache.has(key)) cache.set(key, fn()); return cache.get(key); };

  function drawChart(curves, guides, T, t, yrange) {
    const col = ink(), L = 58, R = 12, Tp = 10, B = 34, pw = CW - L - R, ph = CH - Tp - B;
    k.clearRect(0, 0, CW, CH);
    const lx = (s) => L + (Math.log10(s + 1) / Math.log10(T + 1)) * pw;
    const [ymin, ymax] = yrange;
    const ly = (y) => Tp + ((ymax - Math.log10(Math.max(y, 10 ** ymin))) / (ymax - ymin)) * ph;
    k.strokeStyle = col; k.fillStyle = col; k.font = font(11); k.lineWidth = 1;
    const step = ymax - ymin > 6 ? 2 : 1;
    for (let e = ymin; e <= ymax; e += step) {
      const y = ly(10 ** e);
      k.globalAlpha = 0.15; k.beginPath(); k.moveTo(L, y); k.lineTo(L + pw, y); k.stroke();
      k.globalAlpha = 0.8; k.textAlign = "right"; k.fillText(e === 0 ? "1" : `1e${e}`.replace("-", "−"), L - 6, y + 4);
    }
    k.textAlign = "center";
    for (const s of [1, 10, 100, 1000].filter((s) => s <= T)) {
      const x = lx(s);
      k.globalAlpha = 0.15; k.beginPath(); k.moveTo(x, Tp); k.lineTo(x, Tp + ph); k.stroke();
      k.globalAlpha = 0.8; k.fillText(String(s), Math.min(x, L + pw - 12), Tp + ph + 14);
    }
    k.globalAlpha = 0.9; k.fillText("oracle calls", L + pw / 2, Tp + ph + 29);
    k.save(); k.translate(10, Tp + ph / 2); k.rotate(-Math.PI / 2); k.fillText("primal gap", 0, 0); k.restore();
    k.textAlign = "left";
    k.save(); k.beginPath(); k.rect(L, Tp, pw, ph); k.clip();
    for (const [fn, , opt = {}] of guides) {
      k.setLineDash(opt.dot ? [2, 3] : [6, 4]); k.globalAlpha = 0.75; k.strokeStyle = col; k.lineWidth = 1.3;
      k.beginPath();
      const from = opt.from ?? 1, to = Math.min(T, opt.to ?? T);
      for (let s = from; s <= Math.max(to, from); s++) {
        const X = lx(s), Y = ly(fn(s)); s > from ? k.lineTo(X, Y) : k.moveTo(X, Y);
      }
      if (to <= from) k.lineTo(lx(from) + 6, ly(fn(from)));
      k.stroke();
      if (opt.to != null) { k.setLineDash([]); k.beginPath(); k.arc(lx(to), ly(fn(to)), 3, 0, 2 * Math.PI); k.stroke(); }
    }
    k.setLineDash([]);
    for (const [ys, color] of curves) {
      k.strokeStyle = color; k.lineWidth = 2; k.globalAlpha = 1; k.beginPath();
      let started = false;
      ys.forEach((y, s) => {
        if (!Number.isFinite(y)) return;
        const X = lx(s), Y = ly(y); started ? k.lineTo(X, Y) : k.moveTo(X, Y); started = true;
      });
      k.stroke();
      if (Number.isFinite(ys[t])) { k.fillStyle = color; k.beginPath(); k.arc(lx(t), ly(ys[t]), 3.5, 0, 2 * Math.PI); k.fill(); }
    }
    k.strokeStyle = col; k.globalAlpha = 0.45; k.setLineDash([2, 3]); k.beginPath();
    k.moveTo(lx(t), Tp); k.lineTo(lx(t), Tp + ph); k.stroke();
    k.restore();
    k.globalAlpha = 1; k.strokeStyle = col; k.fillStyle = col;
    legend.replaceChildren();
    for (const [ys, color, label, exact] of curves) {
      const li = elt("li"); const sw = elt("span", "fs-swatch"); sw.style.background = color;
      li.append(sw, elt("span", "fs-name", label),
        elt("span", "fs-val", Number.isFinite(ys[t]) ? fmt(ys[t], exact) : "–"));
      legend.append(li);
    }
    for (const [, label, opt = {}] of guides) {
      const li = elt("li", "fs-guide");
      li.append(elt("span", opt.dot ? "fs-swatch fs-dash fs-dot" : "fs-swatch fs-dash"), elt("span", "fs-name", label));
      legend.append(li);
    }
  }

  function drawPlanar(t) {
    const col = ink(), body = model.get("body"), c = [Number(model.get("cx")), Number(model.get("cy"))];
    const T = HORIZON.planar;
    const S = memo(`p:${body}:${c}`, () => simulatePlanar(body, c, T));
    g.beginPath();
    for (let i = 0; i <= 180; i++) {
      const th = (2 * Math.PI * i) / 180, p = toPx(S.lmoC([-Math.cos(th), -Math.sin(th)]));
      i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1]);
    }
    g.closePath(); g.fillStyle = "#2e86ab22"; g.fill(); g.strokeStyle = "#2e86ab"; g.lineWidth = 2; g.stroke();
    for (const [path, calls, color] of [[S.fwPath, S.calls.fw, COLORS.a], [S.qmPath, S.calls.qm, COLORS.b],
      [S.jmPath, S.calls.jm, COLORS.c]]) {
      let last = -1; while (last + 1 < path.length && calls[last + 1] <= t) last++;
      if (last < 0) continue;
      g.strokeStyle = color; g.globalAlpha = 0.55; g.lineWidth = 1.2; g.beginPath();
      path.slice(Math.max(0, last - 200), last + 1).forEach((p, i) => {
        const q = toPx(p); i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1]);
      });
      g.stroke(); g.globalAlpha = 1;
      const q = toPx(path[last]); g.fillStyle = color; g.beginPath(); g.arc(q[0], q[1], 3.5, 0, 2 * Math.PI); g.fill();
    }
    const xs = toPx(S.xstar), cp = toPx(c);
    g.strokeStyle = col; g.lineWidth = 1.5; g.beginPath(); g.arc(xs[0], xs[1], 5, 0, 2 * Math.PI); g.stroke();
    g.strokeStyle = COLORS.d; g.lineWidth = 2; g.beginPath(); g.arc(cp[0], cp[1], 7, 0, 2 * Math.PI); g.stroke();
    g.fillStyle = col; g.font = font(13); g.fillText("x⋆", xs[0] + 8, xs[1] - 6);
    g.fillStyle = COLORS.d; g.fillText("c", cp[0] + 9, cp[1] + 15);
    const guides = [];
    if (S.delta > 0) guides.push([(s) => 2 * S.delta ** 2 / (s + 1), "bound 2δ²/(t + 1), Frank–Wolfe on K"]);
    if (S.rate) guides.push([S.rate, "linear rate (inner and outer tangent balls)"]);
    drawChart([[byCalls(S.fw, S.calls.fw, T), COLORS.a, "Frank–Wolfe"],
      [byCalls(S.qm, S.calls.qm, T), COLORS.b, "Frank–Wolfe on K"],
      [byCalls(S.jm, S.calls.jm, T), COLORS.c, "projected gradient"]], guides, T, t, [-9, 1]);
    geo.setAttribute("aria-label", "The body, the target c, the minimizer and the iterates; drag to move c");
    caption.textContent = "Drag c. The curves show the smallest primal gap reached so far.";
    return T;
  }

  function drawHard(t) {
    const col = ink(), kk = Number(model.get("k")) || 2, rule = model.get("rule") || "vertex";
    const T = HORIZON.hard;
    const S = memo(`h:${kk}:${rule}`, () => simulateHard(kk, rule, T));
    const inI = new Set(S.indexSet), found = new Set();
    for (let s = 0; s <= t && s < S.found.length; s++) for (const j of S.found[s]) found.add(j);
    const cols = 2 ** Math.ceil(Math.log2(Math.sqrt(S.N))), rows = S.N / cols;
    const cell = Math.floor(256 / cols), x0 = (W - cols * cell) / 2, y0 = 12;
    for (let i = 0; i < S.N; i++) {
      const cx = x0 + (i % cols) * cell, cy = y0 + Math.floor(i / cols) * cell;
      if (found.has(i)) { g.fillStyle = COLORS.d; g.globalAlpha = 1; }
      else if (inI.has(i)) { g.fillStyle = col; g.globalAlpha = 0.55; }
      else { g.fillStyle = col; g.globalAlpha = 0.08; }
      g.fillRect(cx + 0.5, cy + 0.5, cell - 1, cell - 1);
    }
    g.globalAlpha = 1; g.fillStyle = col; g.font = font(12);
    const yt = y0 + rows * cell + 22;
    g.fillText(`${S.N} indices; I contains ${S.d} of them.`, 12, yt);
    const key = (color, alpha, text, y) => {
      g.globalAlpha = alpha; g.fillStyle = color; g.fillRect(12, y - 9, 10, 10);
      g.globalAlpha = 1; g.fillStyle = col; g.fillText(text, 28, y);
    };
    key(COLORS.d, 1, `in I and found after ${t} calls: ${found.size}`, yt + 20);
    key(col, 0.55, "in I, not yet found", yt + 38);
    drawChart([[byCalls(S.fw, S.calls.fw, T), COLORS.a, "Frank–Wolfe"],
      [byCalls(S.qm, S.calls.qm, T), COLORS.b, "Frank–Wolfe on K"],
      [byCalls(S.probe, S.calls.qm, T), COLORS.d, "reads I off the answer", rule === "barycenter"]],
      [[(s) => 2 * S.delta ** 2 / (s + 1), "bound 2δ²/(t + 1) of Frank–Wolfe on K"],
        [() => S.lower, `threshold 1/(16k) for k − 1 = ${kk - 1} call${kk === 2 ? "" : "s"}`,
          { dot: true, from: 0, to: kk - 1 }]], T, t, [-9, 1]);
    geo.setAttribute("aria-label", "The indices; filled: indices of I found by Frank–Wolfe on K so far");
    caption.textContent = {
      vertex: "Each answer of the vertex LMO reveals one index of I: the first in the order of the query.",
      barycenter: "The answer to the vertical call is the barycenter of the bottom face; it reveals all of I at once.",
      unique: "With perturbed vertices every minimizer is unique; the indices of I with positive weight in an " +
        "answer are revealed, one per answer until the iterates approach the minimizer.",
    }[rule];
    return T;
  }

  function drawHilbert(t) {
    const col = ink(), T = HORIZON.hilbert;
    const S = memo("hilbert", () => simulateHilbert(T));
    const x = S.charts[t];
    let last = 0; for (let i = 0; i < x.length; i++) if (Math.abs(x[i]) > 1e-15) last = i;
    const used = last + 1;
    let hi = 0, lo = 0, mass = 0, sq = 0;
    for (let i = 0; i < used; i++) { hi = Math.max(hi, x[i]); lo = Math.min(lo, x[i]); mass += x[i]; sq += x[i] * x[i]; }
    const left = 36, right = W - 12, top = 18, bottom = 210, span = hi - lo || 1;
    const yv = (v) => top + ((hi - v) / span) * (bottom - top);
    g.strokeStyle = col; g.globalAlpha = 0.3; g.lineWidth = 1; g.beginPath();
    g.moveTo(left, yv(0)); g.lineTo(right, yv(0)); g.stroke(); g.globalAlpha = 1;
    const bw = (right - left) / used;
    g.fillStyle = COLORS.a;
    for (let i = 0; i < used; i++) {
      const y1 = yv(Math.max(0, x[i])), y2 = yv(Math.min(0, x[i]));
      g.fillRect(left + i * bw, y1, Math.max(bw - (bw > 3 ? 1 : 0), 0.6), Math.max(y2 - y1, 0.5));
    }
    g.fillStyle = col; g.font = font(11); g.textAlign = "right";
    g.fillText(hi.toFixed(hi < 0.1 ? 3 : 2), left - 4, top + 4); g.fillText("0", left - 4, yv(0) + 4);
    g.textAlign = "center"; g.fillText(`coordinate i = 0, …, ${used - 1}`, (left + right) / 2, bottom + 16);
    g.textAlign = "left"; g.font = font(12);
    const e2 = (v) => v.toExponential(2).replace("-", "−");
    g.fillText(`Frank–Wolfe iterate after ${t} call${t === 1 ? "" : "s"}:`, 12, bottom + 40);
    g.fillText(`Σ xᵢ = ${mass.toFixed(3)},   Σ xᵢ² = ${e2(sq)}`, 12, bottom + 58);
    g.fillText(`(Σ xᵢ)²/(t + 1) = ${e2(mass * mass / (t + 1))}`, 12, bottom + 76);
    const steps = S.open.map((_, s) => s);
    drawChart([[byCalls(S.open, steps, T), COLORS.a, "Frank–Wolfe, step 2/(t + 2)"],
      [byCalls(S.line, steps, T), COLORS.b, "Frank–Wolfe, line search"],
      [byCalls(S.vertical, steps, T), COLORS.d, "one call in the vertical direction", true]],
      [[S.upper, "upper bound 2(15/4)²/(t + 2)"], [S.lower, "lower bound 31/(256(t + 1))", { dot: true }]],
      T, t, [-4, 1]);
    geo.setAttribute("aria-label", "The coordinates of the horizontal part of the Frank–Wolfe iterate");
    caption.textContent = "The bars show the coordinates xᵢ of the Frank–Wolfe iterate. Each call adds at most one " +
      "coordinate and Σ xᵢ stays at least 1/2, so Σ xᵢ² ≥ (Σ xᵢ)²/(t + 1): the primal gap stays above " +
      "31/(256(t + 1)). A single call in the vertical direction returns the minimizer.";
    return T;
  }

  function draw() {
    const mode = modeOf();
    for (const [b, pressed] of buttons) b.setAttribute("aria-pressed", String(pressed()));
    rowBody.hidden = mode !== "planar"; rowK.hidden = rowLMO.hidden = mode !== "hard";
    geo.style.cursor = mode === "planar" ? "crosshair" : "default";
    const sv = model.get("t") == null ? 100 : Number(model.get("t"));
    slider.value = String(sv);
    const T = HORIZON[mode], t = Math.max(1, Math.min(T, Math.round(T ** (sv / 100))));
    tOut.textContent = `t = ${t}`;
    g.clearRect(0, 0, W, H);
    if (mode === "hard") drawHard(t); else if (mode === "hilbert") drawHilbert(t); else drawPlanar(t);
  }

  let dragging = false;
  const moveTo = (ev) => {
    if (modeOf() !== "planar") return;
    const r = geo.getBoundingClientRect();
    const px = ((ev.clientX - r.left) / r.width) * W, py = ((ev.clientY - r.top) / r.height) * H;
    model.set("cx", Math.round(((px / W) * 2 * VIEW - VIEW) * 1000) / 1000);
    model.set("cy", Math.round((VIEW - (py / H) * 2 * VIEW) * 1000) / 1000);
  };
  geo.addEventListener("pointerdown", (ev) => {
    if (modeOf() !== "planar") return;
    dragging = true; geo.setPointerCapture(ev.pointerId); moveTo(ev);
  });
  geo.addEventListener("pointermove", (ev) => { if (dragging) moveTo(ev); });
  geo.addEventListener("pointerup", () => { dragging = false; });
  for (const key of ["body", "cx", "cy", "k", "rule", "t"]) model.on(`change:${key}`, draw);
  draw();
}

export default { render };
