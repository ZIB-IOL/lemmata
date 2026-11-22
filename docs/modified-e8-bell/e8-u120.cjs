"use strict";
function check(condition, detail) {
  if (!condition) throw new Error(detail);
}
function dot(x, y) {
  let sum = 0;
  for (let i = 0; i < x.length; ++i) sum += x[i]*y[i];
  return sum;
}
function doubledRoots() {
  const roots = [];
  for (let i=0; i<8; ++i) for (let j=i+1; j<8; ++j) {
    for (const sign of [-1,1]) {
      const row = Array(8).fill(0);
      row[i] = 2; row[j] = 2*sign;
      roots.push(row);
    }
  }
  for (let mask=0; mask<128; ++mask) {
    const tail = Array.from({length:7}, (_,i) => (mask >> i)&1 ? -1 : 1);
    if (tail.reduce((a,b) => a*b, 1) === 1) roots.push([1,...tail]);
  }
  return roots;
}
function inDoubledLattice(x) {
  return x.every(Number.isInteger) && x.every(v => (v-x[0])%2 === 0)
         && x.reduce((a,b) => a+b,0)%4 === 0;
}
function matrixTest(matrix) {
  const roots = doubledRoots();
  check(matrix.length === 120 && matrix.every(r => r.length === 120 && r.every(Number.isInteger)), "matrix shape or entry");
  const gram = matrix.map((r,i) => r.map((v,j) => (v+13*Number(i===j))/3));
  const keys = [0,1,3,6,10,15,21];  // Zero-based published indices.
  const signedRoots = gram.map(r => {
    const x0 = r[0]-r[28];
    return [x0,...keys.map(j => x0-2*r[j])];
  });
  const signedId = new Map();
  roots.forEach((x,i) => {
    signedId.set(x.join(","),i+1);
    signedId.set(x.map(v=>-v).join(","),-i-1);
  });
  const permutation = signedRoots.map(x => signedId.get(x.join(",")));
  check(permutation.every(Number.isInteger) && new Set(permutation.map(Math.abs)).size===120, "signed permutation");
  const frame = Array.from({length:8}, (_,i) => Array.from({length:8}, (_,j) =>
    roots.reduce((total,r)=>total+r[i]*r[j],0)));
  check(frame.every((r,i)=>r.every((x,j)=>x===120*Number(i===j))), "frame identity");
  const alpha = Array.from({length:8},(_,i)=>roots.reduce((total,r)=>total+r[i],0)/2);
  check(inDoubledLattice(alpha), "sum of representatives in twice the lattice");
  const abit = "010001011001101101111101110101100110111101111101100100111101110011111101010000001000000011101101111111111000010001101000";
  const bbit = "011101011001101111111101110101100110111101111001110110111101011011101101000000001000010011111101111111101000000011001000";
  function transport(bits) {
    check(bits.length===120 && /^[01]+$/.test(bits), "sign string");
    return permutation.map(j => (bits[Math.abs(j)-1]==="1" ? 1 : -1)*Math.sign(j));
  }
  const a=transport(abit), b=transport(bbit);
  let objective=0;
  for (let i=0;i<120;++i) for (let j=0;j<120;++j) {
    check(dot(signedRoots[i],signedRoots[j])===4*gram[i][j], "published Gram entry "+i+","+j);
    objective+=a[i]*matrix[i][j]*b[j];
  }
  check(objective===6104, "lower witness score");
  return {checkedEntries:14400, objective, alpha,
          a:a.map(v=>v===1?"1":"0").join(""), b:b.map(v=>v===1?"1":"0").join(""), permutation};
}

function shortCertificate(limit=620) {
  // Rows are twice the fundamental weights in the indicated E8 basis.
  const weights=[
    [0,0,0,0,0,0,0,4], [1,1,1,1,1,1,1,5], [-1,1,1,1,1,1,1,7],
    [0,0,2,2,2,2,2,10], [0,0,0,2,2,2,2,8], [0,0,0,0,2,2,2,6],
    [0,0,0,0,0,2,2,4], [0,0,0,0,0,0,2,2]
  ];
  const simple=[[1,-1,-1,-1,-1,-1,-1,1],[2,2,0,0,0,0,0,0]];
  for (let i=0; i<6; ++i) {
    const r=Array(8).fill(0); r[i]=-2; r[i+1]=2; simple.push(r);
  }
  const roots=doubledRoots();
  const allRoots=new Set(roots.flatMap(r=>[r.join(","),r.map(v=>-v).join(",")]));
  check(simple.every(r=>allRoots.has(r.join(","))), "simple roots");
  check(weights.every(inDoubledLattice), "fundamental weights in L");
  check(simple.every((a,i)=>weights.every((w,j)=>dot(a,w)===4*Number(i===j))), "dual basis");
  const grams=weights.map(w=>weights.map(q=>dot(w,q)/4));
  check(grams.flat().every(x=>Number.isInteger(x)&&x>0), "positive weight Gram entries");
  const coefficients=roots.map(r=>{
    const c=weights.map(w=>dot(r,w)/4);
    const orientation=c.find(x=>x!==0)>0 ? 1 : -1;
    const pos=c.map(x=>orientation*x);
    check(pos.every(x=>Number.isInteger(x)&&x>=0), "chamber orientation");
    return pos;
  });
  const twiceRho=Array(8).fill(0);
  roots.forEach(r=>{
    const s=Math.sign(weights.reduce((sum,w)=>sum+dot(r,w),0));
    check(s!==0,"positive root choice");
    r.forEach((v,i)=>twiceRho[i]+=s*v/2);
  });
  check(dot(twiceRho,twiceRho)===2480,"chamber radius");
  const label=Array(8).fill(0);
  let count=0, max=-Infinity, atMax=[], runnerUp=-Infinity;
  function visit(i,norm) {
    if (i===8) {
      let score=-12*norm;
      for (const c of coefficients) score+=Math.max(13,12*dot(c,label)-13);
      ++count;
      if (score>max) { runnerUp=max; max=score; atMax=[]; }
      else if (score<max) runnerUp=Math.max(runnerUp,score);
      if (score===max) atMax.push({label:label.slice(), norm});
      return;
    }
    let mixed=0;
    for (let j=0;j<i;++j) mixed+=label[j]*grams[i][j];
    for (let k=0; ; ++k) {
      const next=norm+2*k*mixed+k*k*grams[i][i];
      if (next>limit) break;
      label[i]=k;
      visit(i+1,next);
    }
    label[i]=0;
  }
  visit(0,0);
  check(max===6104 && runnerUp===6094, "one-sign upper");
  check((limit===620 && count===18454 && atMax.length===3) ||
        (limit===900 && count===53407 && atMax.length===4), "shell count");
  return {count, max, atMax, runnerUp, twiceRho};
}

function* enumerateDominant() {
  // x = 2u.  The closed chamber is |x[0]| <= x[1] <= ... <= x[6]
  // and x[7] >= -x[0]+x[1]+...+x[6].
  const x = Array(8).fill(0);
  const masks = [];
  for (let index = 0; index < 128; ++index) {
    const signs = Array.from({length:7}, (_, j) => (index >> j) & 1 ? -1 : 1);
    if (signs.reduce((a, b) => a*b, 1) === 1) masks.push(signs);
  }
  const counts = {vectors:0, rawMax:-Infinity, correctedMax:-Infinity,
                  atCorrectedMax:0, aboveTarget:0, rawExceptions:[], equalityVectors:[]};
  const positivePart = k => Math.max(0, 6*Math.abs(k) - 26);
  function score(norm) {
    ++counts.vectors;
    let raw = 1560 - 3*norm;
    for (let i=0; i<8; ++i) {
      for (let j=i+1; j<8; ++j) {
        raw += positivePart((x[i]+x[j])/2) + positivePart((x[i]-x[j])/2);
      }
    }
    for (const t of masks) {
      const k = (x[0]+t[0]*x[1]+t[1]*x[2]+t[2]*x[3]+t[3]*x[4]
                 +t[4]*x[5]+t[5]*x[6]+t[6]*x[7])/4;
      raw += positivePart(k);
    }
    // u in 2L iff u/2=x/4 in L. For an even x this requires equal
    // residues of x_i mod 4 and sum(x_i) divisible by 8.
    const zeroCoset = x[0]%2 === 0 && x.every(v => (v-x[0])%4 === 0)
                         && x.reduce((sum,v) => sum+v,0)%8 === 0;
    const penaltyNorm = zeroCoset ? 0 : norm%4 === 2 ? 2 : 4;
    const corrected = raw-3*penaltyNorm;
    counts.rawMax = Math.max(counts.rawMax, raw);
    if (corrected > counts.correctedMax) {
      counts.correctedMax = corrected;
      counts.atCorrectedMax = 0;
    }
    if (corrected === counts.correctedMax) ++counts.atCorrectedMax;
    if (corrected > 6104) ++counts.aboveTarget;
    if (corrected === 6104) counts.equalityVectors.push(x.slice());
    if (raw > 6104) counts.rawExceptions.push({x:x.slice(), norm, raw, penaltyNorm, corrected});
  }
  const radius = 4*2480;
  function extend(index, partialSquare, wall) {
    if (index === 7) {
      // wall = -x0 + sum(x1..x6). Choose a parity-compatible x7.
      const first = wall + (Math.abs(wall-x[0])%2);
      for (let last=first; partialSquare+last*last <= radius; last+=2) {
        x[7] = last;
        if ((wall + 2*x[0] + last)%4 === 0) score((partialSquare+last*last)/4);
      }
      return;
    }
    const minimum = index === 1 ? Math.abs(x[0]) : x[index-1];
    const remaining = 7-index;
    for (let v=minimum; ; v+=2) {
      // All remaining chain entries are at least v.
      const minLast = wall+remaining*v;
      if (partialSquare+remaining*v*v+minLast*minLast > radius) break;
      x[index] = v;
      extend(index+1, partialSquare+v*v, wall+v);
    }
  }
  for (let first=-99; first<=99; ++first) {
    x[0] = first;
    extend(1, first*first, -first);
    if (first%4===0) yield first;
  }
  check(counts.vectors===1226617 && counts.rawMax===6116 && counts.correctedMax===6104 &&
        counts.atCorrectedMax===10 && counts.rawExceptions.length===11 && counts.aboveTarget===0,
        "two-sign enumeration");
  return counts;
}

function optimalSupport(equalityVectors) {
  const roots=doubledRoots(), outcomes=[];
  for (const x of equalityVectors) {
    const sum=Array(8).fill(0), unused=[];
    for (const r of roots) {
      const h=dot(r,x)/4;
      check(Number.isInteger(h), "integral height");
      if (Math.abs(h)<5) unused.push(r);
      else for (let j=0;j<8;++j) sum[j]+=Math.sign(h)*r[j];
    }
    if (!sum.every((v,j)=>v===x[j])) continue;
    // Enumerate complement signs by a Gray code. The vector z2 is twice z.
    const z2=Array(8).fill(0);
    for (const r of unused) for (let j=0;j<8;++j) z2[j]-=r[j];
    let minNorm=Infinity, attaining=0;
    for (let i=0;i<2**unused.length;++i) {
      if (i) {
        const bit=31-Math.clz32(i&-i);
        const step=((i^(i>>1)) & (1<<bit)) ? 2 : -2;
        for (let j=0;j<8;++j) z2[j]+=step*unused[bit][j];
      }
      const n=dot(z2,z2)/4;
      if (n<minNorm) {minNorm=n; attaining=0;}
      if (n===minNorm) ++attaining;
    }
    outcomes.push({doubledU:x,support:120-unused.length,minNorm,attaining});
  }
  check(outcomes.length===2 && outcomes.some(o=>o.support===98 && o.minNorm===2 && o.attaining===5280) &&
        outcomes.some(o=>o.support===104 && o.minNorm===4 && o.attaining===576), "equality classes");
  return outcomes;
}

const publishedOrder = [1,3,15,5,17,27,7,19,29,37,9,21,31,39,45,11,23,33,41,47,51,13,25,35,43,49,53,55,-2,-4,-16,-6,-18,-28,-8,-20,-30,-38,-10,-22,-32,-40,-46,-12,-24,-34,-42,-48,-52,-14,-26,-36,-44,-50,-54,-56,105,97,93,91,90,89,-88,117,115,114,113,-64,111,110,109,-68,108,107,-70,106,-71,-72,103,102,101,-76,100,99,-78,98,-79,-80,96,95,-82,94,-83,-84,92,-85,-86,-87,120,119,-58,118,-59,-60,116,-61,-62,-63,112,-65,-66,-67,-69,104,-73,-74,-75,-77,-81,-57];
const expectedSHA256 = "70775ad02f460c1d03f9a7144ce322f2864794311e6e72fbe725a485ef631094";
function publishedSnapshot() {
  const roots=doubledRoots();
  const rows=publishedOrder.map(k=>roots[Math.abs(k)-1].map(x=>Math.sign(k)*x));
  return rows.map((r,i)=>rows.map((s,j)=>3*dot(r,s)/4-13*Number(i===j)));
}
function checkInput(matrix) {
  const result=matrixTest(matrix);
  check(result.permutation.every((k,i)=>k===publishedOrder[i]),"different input ordering");
  return result;
}
function parseMatrix(text) {
  return text.trim().split(/\r?\n/).map(line=>line.trim().split(/\s+/).map(value=>{
    check(/^-?\d+$/.test(value),"non-integer token"); return Number(value);
  }));
}

function visibilityCertificate(game) {
  // First 120 are the canonical doubled roots. The second half contains their negatives.
  const lines=doubledRoots(), roots=lines.concat(lines.map(r=>r.map(x=>-x)));
  const ids=new Map(roots.map((r,i)=>[r.join(","),i]));
  const simple=[[1,-1,-1,-1,-1,-1,-1,1],[2,2,0,0,0,0,0,0]];
  for (let i=0;i<6;++i) {
    const g=Array(8).fill(0); g[i]=-2; g[i+1]=2; simple.push(g);
  }
  const actions=simple.map(g=>{
    const perm=roots.map(r=>{
      const coeff=dot(r,g)/4;
      return ids.get(r.map((x,j)=>x-coeff*g[j]).join(","));
    });
    check(perm.every(Number.isInteger) && new Set(perm).size===240,"root reflection");
    check(perm.every((v,i)=>perm[v]===i),"reflection involution");
    return perm;
  });

  // Recover the 104-agreement witness from its checked published-order strings.
  const hi={a:Array(120),b:Array(120)};
  publishedOrder.forEach((order,i)=>{
    const j=Math.abs(order)-1;
    hi.a[j]=Math.sign(order)*(game.a[i]==="1"?1:-1);
    hi.b[j]=Math.sign(order)*(game.b[i]==="1"?1:-1);
  });
  // Build the 98-agreement cyclic-tournament witness in canonical coordinates.
  const lo={a:Array(120).fill(1),b:Array(120).fill(1)};
  const h=ids.get(simple[0].join(","));
  check(h<120,"exceptional half-root orientation");
  lo.b[h]=-1;
  function orient(r,difference) {
    const id=ids.get(r.join(","));
    check(Number.isInteger(id),"tournament line");
    const sign=id<120?1:-1;
    lo.a[id%120]=sign; lo.b[id%120]=difference?-sign:sign;
  }
  for (let j=1;j<=7;++j) for (let k=j+1;k<=7;++k) {
    const plus=Array(8).fill(0);
    plus[j]=j===7?-2:2; plus[k]=k===7?-2:2;
    orient(plus,false);
    const minus=plus.slice(); minus[k]=-minus[k];
    orient(k-j<=3 ? minus : minus.map(x=>-x),true);
  }
  function witnessTotals(w) {
    let gramValue=0;
    for (let i=0;i<120;++i) for (let j=0;j<120;++j)
      gramValue+=w.a[i]*w.b[j]*dot(lines[i],lines[j])/4;
    const trace=dot(w.a,w.b);
    return {trace,gramValue,bell:3*gramValue-13*trace};
  }
  const totals=[witnessTotals(lo),witnessTotals(hi)];
  check(totals[0].trace===76 && totals[1].trace===88 &&
        totals.every(w=>w.bell===6104),"both maximizing witnesses");
  function lift(signs) { return signs.concat(signs.map(v=>-v)); }
  const a0=lift(lo.a), b0=lift(lo.b), a1=lift(hi.a), b1=lift(hi.b);
  const pairCount=240*240, orbit=new Int32Array(pairCount).fill(-1);
  const queue=new Int32Array(pairCount), classes=[];
  for (let start=0;start<pairCount;++start) {
    if (orbit[start]>=0) continue;
    const id=classes.length;
    queue[0]=start; orbit[start]=id;
    let tail=1, lowSum=0, highSum=0;
    const product=dot(roots[Math.floor(start/240)],roots[start%240]);
    for (let head=0;head<tail;++head) {
      const pair=queue[head],i=Math.floor(pair/240),j=pair%240;
      check(dot(roots[i],roots[j])===product,"orbit preserves dot product");
      lowSum+=a0[i]*b0[j]; highSum+=a1[i]*b1[j];
      for (const perm of actions) {
        const next=240*perm[i]+perm[j];
        if (orbit[next]<0) { orbit[next]=id; queue[tail++]=next; }
      }
    }
    classes.push({product,size:tail,lowSum,highSum});
  }
  const orbitSizes={8:240,4:13440,0:30240,"-4":13440,"-8":240};
  check(classes.length===5 && new Set(classes.map(q=>q.product)).size===5 &&
        classes.every(q=>q.size===orbitSizes[q.product]),"complete ordered-pair orbits");
  // Uniform group elements send a fixed ordered pair uniformly over its orbit.
  // P_ij = product/8, so the identity below verifies (8 R76 + 3 R88)/11.
  for (let i=0;i<120;++i) for (let j=0;j<120;++j) {
    const c=classes[orbit[240*i+j]];
    check(165*8*(8*c.lowSum+3*c.highSum)===109*11*c.size*dot(lines[i],lines[j]),
          "entrywise radial mixture");
  }
  return {witnesses:totals,orbits:classes.sort((a,b)=>b.product-a.product),
          checkedEntries:14400,weights:["8/11","3/11"],visibility:"109/165"};
}

function fixedRootShiftChecks() {
  // Each row uses the two contact strategies and the exact scaled classical
  // upper bound from the companion Fishburn–Reeds certificate.
  // d, t numerator/denominator, scaled bound, traces, left weight, visibility.
  const data=[
    [7,8,1,804,30,12,13,14,67,98],
    [8,36,5,6600,40,30,23,29,275,406],
    [9,8,1,1944,54,48,1,10,27,40],
    [10,84,11,30780,72,50,8,17,57,85]
  ];
  return data.map(([d,A,B,C,tLeft,tRight,f,g,p,q])=>{
    const N=d*(d-1),target=N*(6*B*(d-1)-A);
    check(C*q===p*target, "D_d Bell visibility");
    check((f*tLeft+(g-f)*tRight)*q===g*N*p, "D_d mixed trace");
    return {d,leftWeight:f+"/"+g,visibility:p+"/"+q};
  });
}

if (typeof module !== "undefined" && typeof require === "function" && require.main === module) {
  const options=process.argv.slice(2);
  const file=options.find(s=>!s.startsWith("--"));
  const matrix=file ? parseMatrix(require("node:fs").readFileSync(file,"utf8")) : publishedSnapshot();
  const normalized=matrix.map(r=>r.join(" ")+"\n").join("");
  const digest=require("node:crypto").createHash("sha256").update(normalized,"ascii").digest("hex");
  check(digest===expectedSHA256,"published matrix SHA-256");
  const game=checkInput(matrix);
  console.log(JSON.stringify({sha256:digest, entries:game.checkedEntries, score:game.objective, a:game.a, b:game.b, short:shortCertificate(), visibility:visibilityCertificate(game), fixedD:fixedRootShiftChecks()},null,2));
  if (options.includes("--wide")) console.log("Frame-only radius", JSON.stringify(shortCertificate(900)));
  if (options.includes("--full")) {
    const scan=enumerateDominant();
    let step=scan.next();
    while (!step.done) step=scan.next();
    console.log(JSON.stringify({weylCoset:step.value, feasibleEquality:optimalSupport(step.value.equalityVectors)},null,2));
  }
}
