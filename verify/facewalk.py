"""
The repaired decomposition algorithm for Theorem 5.6.

Instead of choosing eps_kappa independently in each component (which produces
non-metrics -- see decomp.py), we walk the minimal face F(d) SEQUENTIALLY:
at the current point p, pick a direction v in the lineality space of the
smallest face containing p, walk to both boundary points, write p as a convex
combination of them, and recurse.  Each leaf is a vertex of Mbar_n.

We record the leaf count and the denominators actually produced.
"""
from itertools import combinations
from fractions import Fraction as Fr
from math import lcm, gcd
import sys, random
from decomp import setup
from faces import face_data, metric_of, den, is_23smooth

def kernel_vector(rows, N):
    """A nonzero exact solution of C x = 0 for the tight rows C, or None."""
    A = [list(map(Fr, r)) for r in rows]
    piv_col = []
    r = 0
    for c in range(N):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x/pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f*y for x, y in zip(A[i], A[r])]
        piv_col.append(c)
        r += 1
        if r == len(A):
            break
    free = [c for c in range(N) if c not in piv_col]
    if not free:
        return None
    f0 = free[0]
    x = [Fr(0)]*N
    x[f0] = Fr(1)
    for i, c in enumerate(piv_col):
        x[c] = -A[i][f0]
    d = 1
    for t in x: d = lcm(d, t.denominator)
    return [t*d for t in x]

def walk(p, rows, N, out, weight):
    tight = [c for (c, r) in rows if sum(Fr(ci)*pi for ci, pi in zip(c, p)) == r]
    v = kernel_vector(tight, N) if tight else [Fr(1)] + [Fr(0)]*(N-1)
    if tight and v is None:
        out.append((tuple(p), weight)); return
    if not tight:
        v = [Fr(0)]*N; v[0] = Fr(1)
    tp, tm = None, None
    for (c, r) in rows:
        cv = sum(Fr(ci)*vi for ci, vi in zip(c, v))
        if cv == 0: continue
        s = (r - sum(Fr(ci)*pi for ci, pi in zip(c, p))) / cv
        if cv > 0: tp = s if tp is None else min(tp, s)
        else:      tm = s if tm is None else max(tm, s)
    assert tp is not None and tm is not None and tm <= 0 <= tp
    if tp == tm == 0:
        out.append((tuple(p), weight)); return
    pplus  = [pi + tp*vi for pi, vi in zip(p, v)]
    pminus = [pi + tm*vi for pi, vi in zip(p, v)]
    if tp == tm:
        walk(pplus, rows, N, out, weight); return
    lam = (0 - tm) / (tp - tm)          # weight on pplus
    walk(pplus,  rows, N, out, weight*lam)
    walk(pminus, rows, N, out, weight*(1-lam))

def run(n, masks):
    E, m, tris, allt = setup(n)
    stats = {"leaves": {}, "den": {}, "ij": {}}
    bad = []
    for mask in masks:
        fd = face_data(n, mask, E, m, tris, allt)
        if fd is None: continue
        N, cidx, sgn, rows = fd
        if N > 13: continue
        out = []
        walk([Fr(0)]*N, rows, N, out, Fr(1))
        # check convex combination reproduces d
        tot = sum(w for _, w in out)
        assert tot == 1, tot
        for g in range(N):
            assert sum(w*Fr(p[g]) for p, w in out) == 0
        stats["leaves"][len(out)] = stats["leaves"].get(len(out), 0) + 1
        for p, w in out:
            vals = metric_of(list(p), mask, m, cidx, sgn)
            q = den(vals)
            stats["den"][q] = stats["den"].get(q, 0) + 1
            if not is_23smooth(q):
                bad.append((mask, p, q))
            else:
                i = j = 0
                t = q
                while t % 2 == 0: t //= 2; i += 1
                while t % 3 == 0: t //= 3; j += 1
                stats["ij"][i+j] = stats["ij"].get(i+j, 0) + 1
                if i + j > N + 1:
                    bad.append((mask, p, q))
    return stats, bad

if __name__ == "__main__":
    for n in (4, 5):
        E, m, _, _ = setup(n)
        st, bad = run(n, range(1 << m))
        print(f"n={n}: leaves {dict(sorted(st['leaves'].items()))}")
        print(f"      denominators {dict(sorted(st['den'].items()))}")
        print(f"      i+j spectrum {dict(sorted(st['ij'].items()))}   violations: {len(bad)}")
        sys.stdout.flush()
    for n in (6, 7):
        E, m, _, _ = setup(n)
        random.seed(31)
        ms = [random.getrandbits(m) for _ in range(3000 if n == 6 else 600)]
        st, bad = run(n, ms)
        print(f"n={n} (random sample): leaves {dict(sorted(st['leaves'].items()))}")
        print(f"      denominators {dict(sorted(st['den'].items()))}")
        print(f"      i+j spectrum {dict(sorted(st['ij'].items()))}   violations: {len(bad)}")
        sys.stdout.flush()
