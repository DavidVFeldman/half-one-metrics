import random, sys
from fractions import Fraction as Fr
from decomp import setup
from faces import face_data, metric_of, den, is_23smooth
from facewalk import walk
for n,tries,minN in ((7,60000,5),(8,40000,6),(9,25000,6)):
    E,m,tris,allt = setup(n)
    random.seed(2026+n)
    spec={}; used=0; maxN=0
    for _ in range(tries):
        mask=random.getrandbits(m)
        fd=face_data(n,mask,E,m,tris,allt)
        if fd is None: continue
        N,cidx,sgn,rows=fd
        if N<minN or N>14: continue
        used+=1; maxN=max(maxN,N)
        out=[]; walk([Fr(0)]*N,rows,N,out,Fr(1))
        assert sum(w for _,w in out)==1
        for p,w in out:
            q=den(metric_of(list(p),mask,m,cidx,sgn))
            spec[q]=spec.get(q,0)+1
    print(f"n={n}: {used} faces with N>={minN} (max N={maxN}); denominators {dict(sorted(spec.items()))}")
    sys.stdout.flush()
