"use strict";
// Run with Node.js: node verify.cjs [F72.txt F90.txt]
function sum(values) { return values.reduce((a, b) => a + b, 0); }
function checkUpper(d, A, B, expected) {
  // Verify B*C_d(A/B) = expected from above. The proof gives the witnesses.
  const E = d * (d - 1) / 2, p = [];
  let maxNum = -1, maxDen = 1;
  function visit(lower) {
    if (p.length < d) {
      for (let x = lower; x < d; x++) { p.push(x); visit(x); p.pop(); }
      return;
    }
    if ((E - sum(p)) % 2 !== 0) return;
    const n = Array(2*d - 1).fill(0);
    for (let i = 0; i < d; i++) for (let j = 0; j < i; j++) {
      n[p[i]-p[j]]++; n[p[i]+p[j]]++;
    }
    const W = sum(n.map((count, w) => count*w));
    let left = (W - 2*sum(p.map(x => x*x))) / 2;
    if (left < 0 || !Number.isInteger(left)) return;
    let val = sum(n.map((count, w) => count*Math.abs(6*B*w-A)));
    let numerator = val, denominator = 1;
    for (let w = 1; w < n.length && left > 0; w++) {
      const gain = 2*Math.min(6*B*w,A);
      const k = Math.min(n[w], Math.floor(left/w));
      val += k*gain; left -= k*w;
      numerator = val;
      if (k < n[w] && left > 0) {
        numerator = val*w + gain*left; denominator = w; break;
      }
    }
    if (numerator*maxDen > maxNum*denominator) {
      maxNum = numerator; maxDen = denominator;
    }
  }
  visit(0);
  if (maxNum !== expected*maxDen) throw Error([d,A,B,maxNum,maxDen,expected].join(" "));
  return expected;
}
function witness(d, groups, A, B) {
  // Groups in ascending target order. A negative first size denotes terminal zeros.
  const N = d*(d-1);
  let loss = 0, h = 0;
  for (const signedSize of groups) {
    const k = Math.abs(signedSize), edges = k*(k-1)/2;
    if (signedSize < 0) {
      for (let j=0; j<k; j++) loss += 4*j*j;
      loss += 4*(edges % 2); h += 2*edges;
    } else {
      if (!(k % 2)) throw Error("nonzero group must have odd size");
      loss += k*(k*k-1)/3; h += edges;
    }
  }
  if (sum(groups.map(Math.abs)) !== d) throw Error("dimension");
  const alpha2 = 2*N*(2*d-1)/3;
  return {scaled: 3*B*(alpha2-loss)-A*(N-2*h), slope: 2*h-N};
}
function compareFile(d, filename) {
  const data = require("node:fs").readFileSync(filename,"utf8").trim().split(/\s+/).map(Number);
  const rows=[];
  for (let i=0;i<d;i++) for(let j=i+1;j<d;j++) for(const s of [1,-1]){
    const row=Array(d).fill(0); row[i]=1; row[j]=s; rows.push(row);
  }
  const N=rows.length;
  if(data.length!==N*N) throw Error("file size");
  for(let i=0;i<N;i++) for(let j=0;j<N;j++){
    const dot=sum(rows[i].map((v,k)=>v*rows[j][k]));
    if(data[N*i+j]!==3*dot-4*Number(i===j)) throw Error("matrix entry");
  }
}
for(let d=2;d<=10;d++){
  const N=d*(d-1), H=2*N*(2*d-3);
  checkUpper(d,4,1,H);
  checkUpper(d,6,1,H-2*N+12*Math.floor(d/3));
}
const cases=[
  [7,8,1,804,[1,3,3],[-4,3]],
  [8,36,5,6600,[-2,3,3],[3,5]],
  [9,8,1,1944,[3,3,3],[-3,3,3]],
  [10,84,11,30780,[1,3,3,3],[5,5]]
];
for(const [d,A,B,C,groupsL,groupsR] of cases){
  checkUpper(d,A,B,C);
  const L=witness(d,groupsL,A,B), R=witness(d,groupsR,A,B);
  const top=B*6*(d-1)-A;
  if(L.scaled!==C || R.scaled!==C || -top*L.slope<=C || -top*R.slope>=C)
    throw Error("supporting lines");
}
if(typeof process!=="undefined" && process.argv && process.argv.length>2){
  if(process.argv.length!==4) throw Error("supply both matrix paths");
  compareFile(9,process.argv[2]); compareFile(10,process.argv[3]);
}
console.log("18 fixed/zero-diagonal checks and 4 global scalar-shift certificates passed.");
