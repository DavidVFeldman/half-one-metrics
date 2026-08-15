"""CONFLICT 2: article 1 sec 6.3 reports 'no upward trend' in exterior-angle mass for
   half-one vertices over 5<=n<=10; article 2 sec 7-8 asserts half-ones dominate
   asymptotically (Gauss-Bonnet).  Extend the same experiment past n=10."""
import numpy as np, sys
from lp import build
from scipy.optimize import linprog
def cls(x,tol=1e-6):
    z=np.abs(x)<tol; o=np.abs(x-1)<tol; h=np.abs(x-0.5)<tol
    if np.all(z|o): return "partition"
    if np.all(h|o): return "half-one"
    if np.all(z|h|o): return "den2-other"
    return "other"
rng=np.random.default_rng(2026)
print(f"{'n':>3} {'partition':>10} {'half-one':>9} {'den<=2':>8} {'other':>7}   trials")
for n,tr in ((5,400),(6,400),(8,300),(10,300),(12,200),(14,200),(16,150),
             (18,150),(20,120),(24,100),(28,80),(32,60),(36,50),(40,40)):
    E,m,A=build(n); b=np.zeros(A.shape[0])
    c={"partition":0,"half-one":0,"den2-other":0,"other":0}
    for _ in range(tr):
        r=linprog(-rng.normal(size=m),A_ub=A,b_ub=b,bounds=[(0,1)]*m,method="highs")
        c[cls(r.x)]+=1
    d2=(c["partition"]+c["half-one"]+c["den2-other"])/tr
    print(f"{n:>3} {c['partition']/tr:>10.3f} {c['half-one']/tr:>9.3f} {d2:>8.3f} {c['other']/tr:>7.3f}   {tr}")
    sys.stdout.flush()
