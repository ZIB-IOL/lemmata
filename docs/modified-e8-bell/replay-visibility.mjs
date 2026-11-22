// Independent integer replay of the exact tables embedded in the Lean certificate.
// Run from any directory with Node.js >= 24; no dependencies or network access.
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {dirname, resolve} from 'node:path';
const here = dirname(fileURLToPath(import.meta.url));
const lean = resolve(here, '../../lean/Lemmata/ModifiedE8Bell');
const check = (ok, message) => { if (!ok) throw new Error(message); };
const stageSource = readFileSync(resolve(lean, 'VisibilityCompute.lean'), 'utf8');
const start = stageSource.indexOf('#[', stageSource.indexOf('def visibilityEncoding'));
const end = stageSource.indexOf('\n\ndef visibilityStages', start);
check(start >= 0 && end > start, 'locate Lean tables');
const stages = JSON.parse(stageSource.slice(start, end).trim().replace(/^#/, '')).map(stage =>
  stage.split(';').map(row => row.split(',').map(Number)));
const witnessSource = readFileSync(resolve(lean, 'Witness.lean'), 'utf8');
const signing = name => {
  const match = witnessSource.match(new RegExp(`def ${name}\\b[\\s\\S]*?"([01]{120})"`));
  check(match, `locate ${name}`);
  return [...match[1]].map(x => x === '1' ? 1 : -1);
};
const a = signing('tournamentA'), b = signing('tournamentB');
const c = signing('witnessA'), d = signing('witnessB');
const roots = [];
for (let i=0;i<8;i++) for (let j=i+1;j<8;j++) for (const s of [-2,2]) {
  const r=Array(8).fill(0); r[i]=2; r[j]=s; roots.push(r);
}
for (let mask=0;mask<128;mask++) {
  const bits=Array.from({length:7},(_,j)=>(mask>>j)&1);
  if (bits.reduce((s,x)=>s+x,0)%2===0) roots.push([1,...bits.map(x=>1-2*x)]);
}
const rootSource = readFileSync(resolve(lean, 'Compute/Raw.lean'), 'utf8');
const rootText = rootSource.slice(rootSource.indexOf('#['), rootSource.lastIndexOf(']')+1);
const leanRoots = JSON.parse(rootText.replaceAll('#[', '[').replace(/,\s*]/g, ']'));
check(JSON.stringify(leanRoots)===JSON.stringify(roots), 'canonical roots match the Lean matrix');
const dot=(x,y)=>x.reduce((s,a,i)=>s+a*y[i],0);
let M=Array.from({length:120},(_,i)=>Array.from({length:120},(_,j)=>8*a[i]*b[j]+3*c[i]*d[j]));
let denominator=11;
for (const stage of stages) {
  check(stage.length>0, 'nonempty average');
  const N=Array.from({length:120},()=>Array(120).fill(0));
  for (const row of stage) {
    check(row.length===120 && row.every(x=>Number.isInteger(x)&&x!==0&&Math.abs(x)<=120), 'signed indices');
    check(new Set(row.map(Math.abs)).size===120, 'permutation');
    for(let i=0;i<120;i++) for(let j=0;j<120;j++)
      N[i][j]+=Math.sign(row[i])*Math.sign(row[j])*M[Math.abs(row[i])-1][Math.abs(row[j])-1];
  }
  M=N; denominator*=stage.length;
}
for(let i=0;i<120;i++) for(let j=0;j<120;j++) {
  const left=1320*M[i][j], right=109*denominator*dot(roots[i],roots[j]);
  check(Number.isSafeInteger(left)&&Number.isSafeInteger(right),'exact integer range');
  check(left===right,`correlation entry ${i},${j}`);
}
console.log(JSON.stringify({stageSizes:stages.map(x=>x.length),denominator,
  checkedEntries:14400,visibility:'109/165',traces:[dot(a,b),dot(c,d)]},null,2));
