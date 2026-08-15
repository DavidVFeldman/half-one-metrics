"""
Independent verification of the combinatorics in
"Half-One Metrics: Extremality, Enumeration, and Decomposition".

A half-one metric on n points is d in {1/2,1}^E, E = edges of K_n.
Work in units of 1/6 later; here store half-edge set S subset E.

Gamma_d : node set = S (half edges), edge for each *degenerate* triangle.
For half-ones the ONLY degenerate configuration is 1/2 + 1/2 = 1, so
[i,j] ~ [j,k]  iff  both half AND [i,k] unital (i.e. not half).
"""
from itertools import combinations, product
from fractions import Fraction
import sys

def edges(n):
    return list(combinations(range(n), 2))

def gamma(n, S):
    """S: frozenset of half edges. Return adjacency dict on S."""
    Sset = S
    adj = {e: set() for e in Sset}
    for (i, j, k) in combinations(range(n), 3):
        for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
            # triangle with apex a: edges (a,b),(a,c) short, (b,c) long
            e1 = (min(a, b), max(a, b))
            e2 = (min(a, c), max(a, c))
            e3 = (min(b, c), max(b, c))
            if e1 in Sset and e2 in Sset and e3 not in Sset:
                adj[e1].add(e2)
                adj[e2].add(e1)
    return adj

def components_bipartite(adj):
    """Return list of (component nodes, is_bipartite, 2-colouring or None)."""
    seen = {}
    comps = []
    for s in adj:
        if s in seen:
            continue
        stack = [s]
        seen[s] = 0
        nodes = [s]
        bip = True
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in seen:
                    seen[v] = 1 - seen[u]
                    nodes.append(v)
                    stack.append(v)
                elif seen[v] == seen[u]:
                    bip = False
        comps.append((nodes, bip, {u: seen[u] for u in nodes}))
    return comps

def extreme_by_criterion(n, S):
    """Theorem 3.1: extreme iff no component of Gamma_d is bipartite."""
    adj = gamma(n, S)
    return all(not bip for (_, bip, _) in components_bipartite(adj))

# ---------- independent extremality test: rank of tight constraints ----------
def extreme_by_rank(n, S):
    """d extreme in Mbar_n  iff  the tight constraints have full rank m.
    Tight constraints for a half-one metric:
      * d_E = 1 for every unital edge E
      * d_ij + d_jk - d_ik = 0 for every degenerate triangle
    (no d_E = 0 constraints since all values are 1/2 or 1)."""
    E = edges(n)
    idx = {e: t for t, e in enumerate(E)}
    m = len(E)
    rows = []
    for e in E:
        if e not in S:
            r = [0] * m
            r[idx[e]] = 1
            rows.append(r)
    for (i, j, k) in combinations(range(n), 3):
        for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
            e1 = (min(a, b), max(a, b))
            e2 = (min(a, c), max(a, c))
            e3 = (min(b, c), max(b, c))
            if e1 in S and e2 in S and e3 not in S:
                r = [0] * m
                r[idx[e1]] += 1
                r[idx[e2]] += 1
                r[idx[e3]] -= 1
                rows.append(r)
    return rank_mod(rows, m) == m

def rank_mod(rows, m):
    """Exact rank over Q via fraction-free Gaussian elimination on ints."""
    rows = [r[:] for r in rows]
    rank = 0
    col = 0
    R = len(rows)
    while col < m and rank < R:
        piv = None
        for r in range(rank, R):
            if rows[r][col] != 0:
                piv = r
                break
        if piv is None:
            col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        pr = rows[rank]
        for r in range(rank + 1, R):
            if rows[r][col] != 0:
                a, b = pr[col], rows[r][col]
                rows[r] = [b * pr[t] - a * rows[r][t] for t in range(m)]
                # keep numbers small
                g = 0
                for x in rows[r]:
                    g = gcd(g, abs(x))
                if g > 1:
                    rows[r] = [x // g for x in rows[r]]
        rank += 1
        col += 1
    return rank

from math import gcd

def bell(n):
    B = [[0] * (n + 1) for _ in range(n + 1)]
    B[0][0] = 1
    for i in range(1, n + 1):
        B[i][0] = B[i - 1][i - 1]
        for j in range(1, i + 1):
            B[i][j] = B[i][j - 1] + B[i - 1][j - 1]
    return B[n][0]

if __name__ == "__main__":
    print("n | 2^C(n,2) | #ex(H_n) [criterion] | #ex [rank test] | B_n | n^(n-2)-n!/2")
    import math
    for n in range(2, 8):
        E = edges(n)
        m = len(E)
        cnt = 0
        cnt_rank = 0
        check_rank = (n <= 6)
        for mask in range(1 << m):
            S = frozenset(E[t] for t in range(m) if (mask >> t) & 1)
            a = extreme_by_criterion(n, S)
            if a:
                cnt += 1
            if check_rank:
                b = extreme_by_rank(n, S)
                if b:
                    cnt_rank += 1
                if a != b:
                    print("   MISMATCH", n, sorted(S), a, b)
        lb = n ** (n - 2) - math.factorial(n) // 2 if n >= 2 else 0
        print(f"{n} | {1<<m} | {cnt} | {cnt_rank if check_rank else '-'} | {bell(n)} | {lb}")
        sys.stdout.flush()
