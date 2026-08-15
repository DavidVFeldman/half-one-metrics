"""Cross-check Theorem 3.1 (odd-cycle criterion) against the definition of
extremality (unique point satisfying its tight constraints -> rank = m)."""
import random, sys
from itertools import combinations
from fractions import Fraction
from fast import setup, extreme

def tight_rows(mask, m, tris):
    rows = []
    for t in range(m):
        if not ((mask >> t) & 1):
            r = [0] * m
            r[t] = 1
            rows.append(r)          # unital edge pinned
    for (u, v, w) in tris:
        if (mask >> u) & 1 and (mask >> v) & 1 and not ((mask >> w) & 1):
            r = [0] * m
            r[u] += 1
            r[v] += 1
            r[w] -= 1
            rows.append(r)          # degenerate triangle
    return rows

def rank(rows, m):
    rows = [[Fraction(x) for x in r] for r in rows]
    rk = 0
    for col in range(m):
        piv = next((r for r in range(rk, len(rows)) if rows[r][col] != 0), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        pr = rows[rk]
        inv = Fraction(1) / pr[col]
        pr = [x * inv for x in pr]
        rows[rk] = pr
        for r in range(len(rows)):
            if r != rk and rows[r][col] != 0:
                f = rows[r][col]
                rows[r] = [a - f * b for a, b in zip(rows[r], pr)]
        rk += 1
    return rk

if __name__ == "__main__":
    for n in (3, 4, 5):
        E, m, tris = setup(n)
        bad = 0
        for mask in range(1 << m):
            a = extreme(mask, m, tris)
            b = (rank(tight_rows(mask, m, tris), m) == m)
            if a != b:
                bad += 1
                if bad < 4:
                    print("  MISMATCH n=%d halfedges=%s criterion=%s rank=%s"
                          % (n, [E[t] for t in range(m) if (mask >> t) & 1], a, b))
        print(f"n={n}: exhaustive {1<<m} half-one metrics, mismatches = {bad}")
        sys.stdout.flush()

    for n in (6, 7, 8):
        E, m, tris = setup(n)
        random.seed(11 + n)
        bad = 0
        N = 3000
        for _ in range(N):
            mask = random.getrandbits(m)
            a = extreme(mask, m, tris)
            b = (rank(tight_rows(mask, m, tris), m) == m)
            if a != b:
                bad += 1
        print(f"n={n}: {N} random half-one metrics, mismatches = {bad}")
        sys.stdout.flush()
