"""
Proposed replacement for Theorem 5.6:

   CONJECTURE (den-3 decomposition).  Every half-one metric d in H_n is a convex
   combination of extreme points of Mbar_n whose denominators divide 3
   (i.e. metrics with values in {0, 1/3, 2/3, 1}).

Test: in the eps-coordinates of the minimal face of d, the candidate points are
eps in {-1/2,-1/6,1/6,1/2}^N (each component pushed to a value producing entries
in {0,1/3,2/3,1}).  Keep those that are metrics AND extreme, then ask whether
0 lies in their convex hull.
"""
from itertools import combinations, product
from fractions import Fraction as Fr
import numpy as np, sys, random
from scipy.optimize import linprog
from decomp import setup, gamma_adj, components, is_metric
from crosscheck import rank

CAND = (Fr(-1,2), Fr(-1,6), Fr(1,6), Fr(1,2))

def extreme_pt(vals, m, allt, E, idx):
    rows = []
    for t in range(m):
        if vals[t] == 0 or vals[t] == 1:
            r = [0]*m; r[t] = 1; rows.append(r)
    for (a,b,c) in allt:
        for (u,v,w) in ((a,b,c),(b,a,c),(c,a,b)):
            if vals[u] == vals[v] + vals[w]:
                r=[0]*m; r[u]+=1; r[v]-=1; r[w]-=1; rows.append(r)
    return rank(rows, m) == m

def test(n, masks, Nmax=8):
    E, m, tris, allt = setup(n)
    idx = {e:t for t,e in enumerate(E)}
    ok = fail = skipped = 0
    failures = []
    for mask in masks:
        adj = gamma_adj(mask, m, tris)
        comps = components(mask, m, adj)
        bip = [s for (s,b) in comps if b]
        if not bip:
            continue                       # extreme already
        N = len(bip)
        if N > Nmax:
            skipped += 1; continue
        cidx, sgn = {}, {}
        for g,s in enumerate(bip):
            for u,x in s.items(): cidx[u]=g; sgn[u]=x
        pts = []
        for eps in product(CAND, repeat=N):
            vals = []
            for t in range(m):
                if (mask>>t)&1:
                    vals.append(Fr(1,2) + sgn[t]*eps[cidx[t]] if t in cidx else Fr(1,2))
                else:
                    vals.append(Fr(1))
            if not is_metric(vals, allt):
                continue
            if not extreme_pt(vals, m, allt, E, idx):
                continue
            pts.append([float(x) for x in eps])
        if not pts:
            fail += 1; failures.append((mask, N, "no candidates")); continue
        A = np.array(pts).T                        # N x P
        P = A.shape[1]
        Aeq = np.vstack([A, np.ones(P)])
        beq = np.zeros(N+1); beq[-1] = 1.0
        res = linprog(np.zeros(P), A_eq=Aeq, b_eq=beq, bounds=[(0,None)]*P,
                      method="highs")
        if res.status == 0:
            ok += 1
        else:
            fail += 1; failures.append((mask, N, "0 not in hull"))
    return ok, fail, skipped, failures, E, m

if __name__ == "__main__":
    for n in (4,5):
        E,m,_,_ = setup(n)
        ok,fail,sk,fl,E,m = test(n, range(1<<m))
        print(f"n={n}: {ok} half-one metrics decompose into extreme "
              f"denominator-dividing-3 metrics; {fail} fail; {sk} skipped (N too large)")
        for mask,N,why in fl[:3]:
            print("   FAIL:", [E[t] for t in range(m) if (mask>>t)&1], "N=",N, why)
        sys.stdout.flush()
    n = 6
    E,m,_,_ = setup(n)
    random.seed(5)
    ms = [random.getrandbits(m) for _ in range(4000)]
    ok,fail,sk,fl,E,m = test(n, ms)
    print(f"n=6 (4000 random): {ok} decompose; {fail} fail; {sk} skipped")
    for mask,N,why in fl[:3]:
        print("   FAIL:", [E[t] for t in range(m) if (mask>>t)&1], "N=",N, why)
