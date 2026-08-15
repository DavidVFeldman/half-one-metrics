"""Check article 1's vertex-denominator profiles by LP sampling with exact rounding."""
import numpy as np, sys
from fractions import Fraction as Fr
from lp import build
from scipy.optimize import linprog
def denom(x, maxq=60, tol=2e-7):
    for q in range(1, maxq+1):
        if np.max(np.abs(q*x-np.round(q*x))) < tol*max(1,q):
            return q
    return None
rng=np.random.default_rng(77)
for n,tr in ((5,3000),(6,3000),(7,3000),(8,2000)):
    E,m,A=build(n); b=np.zeros(A.shape[0])
    spec={}
    for _ in range(tr):
        r=linprog(-rng.normal(size=m),A_ub=A,b_ub=b,bounds=[(0,1)]*m,method="highs")
        q=denom(r.x); spec[q]=spec.get(q,0)+1
    tot=sum(spec.values())
    print(f"n={n} ({tr} objectives): " +
          ", ".join(f"den {k}: {v} ({100*v/tot:.2f}%)"
                    for k,v in sorted(spec.items(), key=lambda kv:(kv[0] is None,kv[0]))))
    sys.stdout.flush()
