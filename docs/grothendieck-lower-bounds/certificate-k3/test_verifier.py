"""Compare independent DFS against exhaustive sign enumeration and bad inputs."""
from pathlib import Path
import itertools,random,subprocess,tempfile,json,os

ROOT=Path(__file__).resolve().parent
BINARY=os.environ.get('VERIFY_BINARY',str(ROOT/'verify_classical'))
rng=random.Random(20261122)

def exact(m):
    if not m:return 0
    return max(sum(abs(sum(a[i]*m[i][j] for i in range(len(m)))) for j in range(len(m[0])))
        for a in itertools.product((-1,1),repeat=len(m)))

def write_matrix(path,m):
    path.write_text('\n'.join(' '.join(map(str,row)) for row in m)+'\n')

checks=0
with tempfile.TemporaryDirectory(dir=ROOT) as tmp:
    d=Path(tmp)
    for case in range(24):
        n=1+case%10;m=1+(case*3)%12
        original=[[rng.randrange(-7,8) for _ in range(m)] for _ in range(n)]
        ordered=original.copy();rng.shuffle(ordered)
        values=[exact(ordered[k:]) for k in range(n)]+[0]
        write_matrix(d/'original',original);write_matrix(d/'ordered',ordered)
        (d/'tails').write_text('\n'.join(map(str,values)))
        base=[BINARY,str(d/'original'),str(d/'ordered'),str(d/'tails')]
        for threads in (1,2):
            p=subprocess.run(base+[str(values[0]),str(threads),'3'],capture_output=True,text=True)
            assert p.returncode==0,(case,p.stdout,p.stderr)
            assert 'VERIFIED classical_upper=' in p.stdout
            checks+=1
            if values[0]:
                p=subprocess.run(base+[str(values[0]-1),str(threads),'2'],capture_output=True,text=True)
                assert p.returncode==1,(case,p.stdout,p.stderr)
                checks+=1
        if n>=2 and values[-2]:
            corrupt=values.copy();corrupt[-2]-=1
            (d/'tails').write_text('\n'.join(map(str,corrupt)))
            p=subprocess.run(base+[str(values[0]),'2'],capture_output=True,text=True)
            assert p.returncode==1,(case,p.stdout,p.stderr)
            checks+=1
    # Reject permutation mismatch and arithmetic outside the stated safe range.
    write_matrix(d/'original',[[1,2],[3,4]]);write_matrix(d/'ordered',[[1,2],[3,5]])
    (d/'tails').write_text('10\n7\n0\n')
    assert subprocess.run(base+['10','1'],capture_output=True).returncode==2;checks+=1
    for name in ('original','ordered'):write_matrix(d/name,[[2147483647]])
    (d/'tails').write_text('2147483647\n0\n')
    assert subprocess.run(base+['2147483647','1'],capture_output=True).returncode==2;checks+=1
    # A failed integer extraction at EOF must not silently drop the final token.
    for token in ('9223372036854775808','-9223372036854775809'):
        for name in ('original','ordered'):(d/name).write_text('1 '+token)
        (d/'tails').write_text('1 0')
        assert subprocess.run(base+['1','1'],capture_output=True).returncode==2;checks+=1
    for name in ('original','ordered'):write_matrix(d/name,[[1]])
    (d/'tails').write_text('1 0 9223372036854775808')
    assert subprocess.run(base+['1','1'],capture_output=True).returncode==2;checks+=1
print(json.dumps({'passed_checks':checks,'cases':24,'comparison':'exhaustive enumeration; exact and too-low full bounds; too-low tail bounds; row permutation and overflow safety rejection'},indent=2))
