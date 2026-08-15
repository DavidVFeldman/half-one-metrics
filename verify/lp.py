"""Random linear optimisation over Mbar_n.

Reproduces the experiment behind Figure 2 (partition metrics vs. extreme
half-one metrics as maximisers of random linear objectives) and records the
denominators of the vertices that turn up.
"""
import numpy as np, sys
from itertools import combinations
from fractions import Fraction
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

def build(n):
    E = list(combinations(range(n), 2))
    idx = {e: t for t, e in enumerate(E)}
    m = len(E)
    rows, cols, data = [], [], []
    r = 0
    for (i, j, k) in combinations(range(n), 3):
        for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
            # d_bc - d_ab - d_ac <= 0
            rows += [r, r, r]
            cols += [idx[(min(b,c),max(b,c))], idx[(min(a,b),max(a,b))],
                     idx[(min(a,c),max(a,c))]]
            data += [1.0, -1.0, -1.0]
            r += 1
    A = csr_matrix((data, (rows, cols)), shape=(r, m))
    return E, m, A

def classify(x, tol=1e-7):
    v = np.round(x, 9)
    if np.all((np.abs(v) < tol) | (np.abs(v-1) < tol)):
        return "partition"
    if np.all((np.abs(v-0.5) < tol) | (np.abs(v-1) < tol)):
        return "half-one"
    return "other"

def denom(x, maxq=5040, tol=1e-6):
    """smallest q<=maxq with q*x all near-integers"""
    for q in range(1, maxq+1):
        if np.max(np.abs(q*x - np.round(q*x))) < tol*q:
            return q
    return None

if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    ns = [int(v) for v in sys.argv[2].split(",")] if len(sys.argv) > 2 else \
         [4,5,6,7,8,10,12,14,16,18,20,22,24]
    rng = np.random.default_rng(20260812)
    print(f"{'n':>3} {'partition':>10} {'half-one':>9} {'other':>7}  denominators seen")
    for n in ns:
        E, m, A = build(n)
        b = np.zeros(A.shape[0])
        cnt = {"partition":0, "half-one":0, "other":0}
        dens = {}
        for _ in range(trials):
            c = rng.normal(size=m)
            res = linprog(-c, A_ub=A, b_ub=b, bounds=[(0,1)]*m, method="highs")
            x = res.x
            k = classify(x)
            cnt[k] += 1
            q = denom(x)
            dens[q] = dens.get(q, 0) + 1
        print(f"{n:>3} {cnt['partition']/trials:>10.3f} {cnt['half-one']/trials:>9.3f} "
              f"{cnt['other']/trials:>7.3f}  {dict(sorted(dens.items(), key=lambda kv:(kv[0] is None, kv[0])))}")
        sys.stdout.flush()
