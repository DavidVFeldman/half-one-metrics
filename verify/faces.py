"""
Exact vertex enumeration of the minimal face F(d) of a half-one metric d.

F(d) = { eps in R^N : d + sum_kappa eps_kappa eta_kappa in Mbar_n },
N = number of BIPARTITE components of Gamma_d (isolated nodes included).

Complete inequality description (verified against brute force in check_desc()):
  (box)  |eps_kappa| <= 1/2
  (tri)  s_u eps_c(u) - s_v eps_c(v) - s_w eps_c(w) <= 1/2
         for every all-half triangle {u,v,w} and each choice of long side,
         terms in rigid components dropped.

We enumerate vertices exactly (Fractions) for N <= NMAX and report the
denominators of the resulting extreme metrics.
"""
from itertools import combinations, product
from fractions import Fraction as Fr
from math import lcm
import sys, random
from decomp import setup, gamma_adj, components, is_metric
from crosscheck import rank

def face_data(n, mask, E, m, tris, allt):
    adj = gamma_adj(mask, m, tris)
    comps = components(mask, m, adj)
    bip = [s for (s, b) in comps if b]
    if not bip:
        return None
    cidx, sgn = {}, {}
    for g, s in enumerate(bip):
        for u, x in s.items():
            cidx[u] = g; sgn[u] = x
    N = len(bip)
    rows = []                      # (coeff vector length N, rhs)  coeff.eps <= rhs
    for g in range(N):
        e = [0]*N; e[g] = 1;  rows.append((tuple(e), Fr(1, 2)))
        e = [0]*N; e[g] = -1; rows.append((tuple(e), Fr(1, 2)))
    for (a, b, c) in allt:
        if not all((mask >> t) & 1 for t in (a, b, c)):
            continue
        for (u, v, w) in ((a,b,c),(b,a,c),(c,a,b)):
            e = [0]*N
            for (t, s) in ((u, 1), (v, -1), (w, -1)):
                if t in cidx:
                    e[cidx[t]] += s * sgn[t]
            if any(e):
                rows.append((tuple(e), Fr(1, 2)))
    rows = list(dict.fromkeys(rows))
    return N, cidx, sgn, rows

def solve(sub, N):
    """exact solve of N equations coeff.eps = rhs; None if singular"""
    A = [list(map(Fr, c)) + [r] for (c, r) in sub]
    for col in range(N):
        piv = next((i for i in range(col, N) if A[i][col] != 0), None)
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for i in range(N):
            if i != col and A[i][col] != 0:
                f = A[i][col]
                A[i] = [x - f*y for x, y in zip(A[i], A[col])]
    return [A[i][N] for i in range(N)]

def vertices(rows, N):
    out = set()
    for sub in combinations(rows, N):
        x = solve(sub, N)
        if x is None:
            continue
        if all(sum(c[i]*x[i] for i in range(N)) <= r + 0 for (c, r) in rows):
            out.add(tuple(x))
    return sorted(out)

def metric_of(eps, mask, m, cidx, sgn):
    return [ (Fr(1,2) + sgn[t]*eps[cidx[t]] if t in cidx else Fr(1,2))
             if (mask >> t) & 1 else Fr(1) for t in range(m) ]

def is_extreme_pt(vals, m, allt):
    rows = []
    for t in range(m):
        if vals[t] == 0 or vals[t] == 1:
            r = [0]*m; r[t] = 1; rows.append(r)
    for (a,b,c) in allt:
        for (u,v,w) in ((a,b,c),(b,a,c),(c,a,b)):
            if vals[u] == vals[v] + vals[w]:
                r=[0]*m; r[u]+=1; r[v]-=1; r[w]-=1; rows.append(r)
    return rank(rows, m) == m

def den(vals):
    d = 1
    for x in vals: d = lcm(d, x.denominator)
    return d

def is_23smooth(q):
    while q % 2 == 0: q //= 2
    while q % 3 == 0: q //= 3
    return q == 1

def run(n, masks, NMAX=4):
    E, m, tris, allt = setup(n)
    spec = {}
    worst = {}
    skipped = 0
    for mask in masks:
        fd = face_data(n, mask, E, m, tris, allt)
        if fd is None: continue
        N, cidx, sgn, rows = fd
        if N > NMAX:
            skipped += 1; continue
        for eps in vertices(rows, N):
            vals = metric_of(eps, mask, m, cidx, sgn)
            assert is_metric(vals, allt)
            q = den(vals)
            spec[q] = spec.get(q, 0) + 1
            if not is_23smooth(q):
                worst.setdefault(q, (mask, eps, vals))
    return spec, worst, skipped, E, m

if __name__ == "__main__":
    for n in (4, 5):
        E, m, _, _ = setup(n)
        spec, worst, sk, E, m = run(n, range(1 << m))
        print(f"n={n} (N<=4, {sk} faces skipped): vertex denominators of minimal faces")
        print("   ", dict(sorted(spec.items())))
        for q, (mask, eps, vals) in worst.items():
            print(f"    !! non-{{2,3}}-smooth denominator {q}: half edges "
                  f"{[E[t] for t in range(m) if (mask>>t)&1]}")
        sys.stdout.flush()
    n = 6
    E, m, _, _ = setup(n)
    random.seed(17)
    ms = [random.getrandbits(m) for _ in range(6000)]
    spec, worst, sk, E, m = run(n, ms)
    print(f"n=6 (6000 random, N<=4, {sk} skipped): {dict(sorted(spec.items()))}")
    for q, (mask, eps, vals) in worst.items():
        print(f"    !! non-{{2,3}}-smooth denominator {q}: half edges "
              f"{[E[t] for t in range(m) if (mask>>t)&1]}")
