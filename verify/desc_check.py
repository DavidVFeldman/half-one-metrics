"""Verify that the inequality description of P_d (box + all-half triangles) is
   COMPLETE: it cuts out exactly the metrics on the affine span of the face."""
import random
from fractions import Fraction as Fr
from decomp import setup, is_metric
from faces import face_data, metric_of
bad=0; tested=0
for n in (5,6,7):
    E,m,tris,allt=setup(n)
    random.seed(4+n)
    for _ in range(4000):
        mask=random.getrandbits(m)
        fd=face_data(n,mask,E,m,tris,allt)
        if fd is None: continue
        N,cidx,sgn,rows=fd
        if N>6: continue
        for _ in range(20):
            eps=[Fr(random.randint(-6,6),12) for _ in range(N)]
            inP=all(sum(Fr(c[i])*eps[i] for i in range(N))<=r for (c,r) in rows)
            isM=is_metric(metric_of(eps,mask,m,cidx,sgn),allt)
            tested+=1
            if inP!=isM: bad+=1
print(f"tested {tested} points; description/metricity disagreements: {bad}")
