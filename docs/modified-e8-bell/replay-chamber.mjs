// Run with Node.js: node replay-chamber.mjs
// All operations below are exact on their integer inputs. The largest
// intermediate values are many orders of magnitude below 2^53.
function check(ok, message) {
  if (!ok) throw new Error(message);
}
function dot(u, v) {
  return u.reduce((sum, x, j) => sum + x * v[j], 0);
}
function rootLines() {
  const rows = [];
  for (let i = 0; i < 8; i++) {
    for (let j = i + 1; j < 8; j++) {
      for (const end of [-2, 2]) {
        const row = Array(8).fill(0);
        row[i] = 2;
        row[j] = end;
        rows.push(row);
      }
    }
  }
  for (let mask = 0; mask < 128; mask++) {
    const row = [1];
    let negatives = 0;
    for (let j = 0; j < 7; j++) {
      const bit = (mask >> j) & 1;
      row.push(1 - 2 * bit);
      negatives += bit;
    }
    if (negatives % 2 === 0) rows.push(row);
  }
  return rows;
}
const roots = rootLines();
function upper(p) {
  let value = -3 * dot(p, p);
  for (const r of roots) value += Math.max(13, 3 * Math.abs(dot(r, p)) - 13);
  return value;
}
function key(p) { return p.join(","); }

function reflectionChecks() {
  const byLine = new Map();
  for (const [i, r] of roots.entries()) {
    byLine.set(key(r), i);
    byLine.set(key(r.map(x => -x)), i);
  }
  check(byLine.size === 240, "root lines");
  const rho = [0, 1, 2, 3, 4, 5, 6, 23];
  const simple = [
    [1,-1,-1,-1,-1,-1,-1,1], [2,2,0,0,0,0,0,0],
    ...Array.from({length: 6}, (_, i) => rho.map((_, j) =>
      j === i ? -2 : (j === i + 1 ? 2 : 0)))
  ];
  for (const g of simple) {
    check(dot(g, g) === 8 && dot(g, rho) === 2, "simple wall or height");
    const image = new Set();
    for (const r of roots) {
      const n = dot(r, g);
      check(n % 4 === 0, "reflection integrality");
      const s = r.map((x,j) => x - (n / 4) * g[j]);
      const i = byLine.get(key(s));
      check(i !== undefined, "reflection closure");
      image.add(i);
    }
    check(image.size === 120, "reflection permutation");
  }
  for (let j = 0; j < 8; j++) {
    const col = roots.map(r => r[j]);
    check(col.reduce((s,x) => s + Math.abs(x), 0) === 92, "coordinate bound");
    check(col.reduce((s,x) => s + x, 0) % 4 === 0, "base sign sum parity");
  }
}

function byCoordinates(visit) {
  for (let first = -46; first <= 46; first++) {
    const p = [first];
    function extend(sum) {
      const slots = 7 - p.length;
      if (slots === 0) {
        // The six middle coordinates have the parity of first, hence
        // sum - first already has that same parity.
        for (let last = sum - first; last <= 46; last += 2) visit([...p,last]);
        return;
      }
      const low = p.length === 1 ? Math.abs(first) : p[p.length-1];
      for (let x = low; sum + slots * x <= 46 + first; x += 2) {
        p.push(x);
        extend(sum + x);
        p.pop();
      }
    }
    extend(0);
  }
}

function byGaps(visit) {
  const weights = [2, 5, 7, 10, 8, 6, 4, 2];
  const gaps = [];
  function extend(budget) {
    if (gaps.length === weights.length) {
      const [d,s,t,a,b,c,e,f] = gaps;
      const p = [s-t,s+t];
      for (const gap of [a,b,c,e,f]) p.push(p[p.length-1] + 2 * gap);
      const last = 2*d + 5*s + 7*t + 10*a + 8*b + 6*c + 4*e + 2*f;
      check(last === 46-budget, "gap reconstruction");
      return visit([...p,last]);
    }
    const w = weights[gaps.length];
    for (let n = 0; w * n <= budget; n++) {
      gaps.push(n);
      extend(budget - w * n);
      gaps.pop();
    }
  }
  extend(46);
}

function replay() {
  reflectionChecks();
  const points = new Map();
  byCoordinates(p => {
    check(!points.has(key(p)), "repeated Cartesian point");
    points.set(key(p), upper(p));
  });
  const gapKeys = new Set();
  const frequencies = new Map();
  byGaps(p => {
    const k = key(p);
    check(!gapKeys.has(k) && points.has(k), "chamber parametrisation");
    gapKeys.add(k);
    const s = points.get(k);
    frequencies.set(s, (frequencies.get(s) || 0) + 1);
  });
  const [maximum, runnerUp] = [...frequencies.keys()].sort((a,b) => b-a);
  check(points.size === 38549 && gapKeys.size === points.size, "case count");
  check(maximum === 6104 && frequencies.get(maximum) === 5 && runnerUp === 6098, "maximum");

  const a = [..."010001011001101101111101110101100110111101111101100100111101110011111101010000001000000011101101111111111000010001101000"].map(c => c === "1" ? 1 : -1);
  const b = [..."011101011001101111111101110101100110111101111001110110111101011011101101000000001000010011111101111111101000000011001000"].map(c => c === "1" ? 1 : -1);
  check(a.length === 120 && b.length === 120, "witness lengths");
  const signed = s => Array.from({length:8}, (_,j) =>
    roots.reduce((n,r,i) => n + s[i] * r[j], 0));
  const fourScore = 3 * dot(signed(a),signed(b)) - 52 * dot(a,b);
  check(fourScore === 4 * 6104, "attaining signs");
  return {chamberPoints: points.size, maximum, ties: frequencies.get(maximum),
    runnerUp, simpleReflections: 8, witnessScore: fourScore / 4};
}
console.log(JSON.stringify(replay(), null, 2));
