"""Exhaustive tests for counterexample export, batching, and enumeration."""
from pathlib import Path
import itertools,random,subprocess,tempfile,json,os
ROOT=Path(__file__).resolve().parent;BINARY=Path(os.environ.get('VERIFY_BINARY',str(ROOT/'verify_classical')));rng=random.Random(731)
def values(M):
    if not M:return [((),0)]
    return [(a,sum(abs(sum(a[i]*M[i][j] for i in range(len(M)))) for j in range(len(M[0]))))
        for a in itertools.product((-1,1),repeat=len(M))]
def exact(M):return max(v for a,v in values(M))
def canonical(a):return tuple(x*a[0] for x in a)
def write(p,M):p.write_text('\n'.join(' '.join(map(str,row)) for row in M)+'\n')
checks=0
with tempfile.TemporaryDirectory(dir=ROOT) as tmp:
 d=Path(tmp)
 for case in range(12):
    n=3+case%6;m=2+case%5
    M=[[rng.randrange(-5,6) for _ in range(m)] for _ in range(n)]
    O=M.copy();rng.shuffle(O)
    write(d/'original',M);write(d/'ordered',O)
    (d/'tails').write_text('\n'.join(map(str,[exact(O[k:]) for k in range(n)]+[0])))
    cutoff=exact(M)//2
    base=[str(BINARY),str(d/'original'),str(d/'ordered'),str(d/'tails'),str(cutoff),'2','2','--counterexample-out',str(d/'examples.json')]
    p=subprocess.run(base+['--enumerate-above'],capture_output=True,text=True)
    assert p.returncode==0 and 'ENUMERATION_COMPLETE' in p.stdout,(p.stdout,p.stderr)
    data=json.loads((d/'examples.json').read_text())
    expected={canonical(a) for a,v in values(M) if v>cutoff}
    got={canonical(e['alice_signs']) for e in data['counterexamples']}
    assert expected==got and data['exhaustive_in_retained_symmetry_prefixes'];checks+=1
    p=subprocess.run(base+['--max-counterexamples','3'],capture_output=True,text=True)
    assert p.returncode==1,(p.stdout,p.stderr)
    data=json.loads((d/'examples.json').read_text())
    assert len(data['counterexamples'])==min(3,len(expected))
    for e in data['counterexamples']:
      a=e['alice_signs'];assert all(x in (-1,1) for x in a)
      v=sum(abs(sum(a[i]*M[i][j] for i in range(n))) for j in range(m))
      assert v==e['value'] and v>cutoff
    checks+=1
 # Duplicate-row permutation plus signed-symmetry orbit coverage in enumeration.
 M=[[1,1,1] for _ in range(4)];write(d/'original',M);write(d/'ordered',M)
 (d/'tails').write_text('12\n9\n6\n3\n0\n')
 perms=list(itertools.permutations(range(4)));lines=['4 3 24','0 1 3']
 for perm in perms:lines+=[' '.join(map(str,perm)),'1 1 1 1','0 1 2','1 1 1']
 (d/'sym').write_text('\n'.join(lines)+'\n')
 cmd=[str(BINARY),str(d/'original'),str(d/'ordered'),str(d/'tails'),'0','2','2','--symmetry',str(d/'sym'),'--enumerate-above','--counterexample-out',str(d/'examples.json')]
 p=subprocess.run(cmd,capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr)
 data=json.loads((d/'examples.json').read_text());expanded=set()
 for e in data['counterexamples']:
    for perm in perms:
      a=e['alice_signs'];expanded.add(canonical([a[i] for i in perm]))
 assert expanded=={canonical(a) for a,v in values(M) if v>0};checks+=1
print(json.dumps({'passed_oracle_mode_checks':checks,'checks':'exact enumeration sets, batching limits and exported original-row signs, duplicate-row signed-symmetry coverage'},indent=2))
