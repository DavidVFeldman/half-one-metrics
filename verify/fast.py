"""Fast enumeration of |ex(H_n)| via the odd-cycle criterion, bitmask version."""
from itertools import combinations
import math, sys

def setup(n):
    E = list(combinations(range(n), 2))
    idx = {e: t for t, e in enumerate(E)}
    m = len(E)
    # tri[t] = list of (u, v, w) index triples: u,v short (share apex), w long
    tris = []
    for (i, j, k) in combinations(range(n), 3):
        for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
            e1 = idx[(min(a, b), max(a, b))]
            e2 = idx[(min(a, c), max(a, c))]
            e3 = idx[(min(b, c), max(b, c))]
            tris.append((e1, e2, e3))
    return E, m, tris

def extreme(mask, m, tris):
    """Gamma_d adjacency as bitmask list; extreme iff no bipartite component."""
    adj = [0] * m
    for (u, v, w) in tris:
        if (mask >> u) & 1 and (mask >> v) & 1 and not ((mask >> w) & 1):
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    rem = mask
    while rem:
        s = (rem & -rem).bit_length() - 1
        # BFS 2-colour
        colour = {s: 0}
        stack = [s]
        comp = 1 << s
        bip = True
        while stack:
            u = stack.pop()
            a = adj[u]
            while a:
                b = a & -a
                v = b.bit_length() - 1
                a ^= b
                if v not in colour:
                    colour[v] = 1 - colour[u]
                    comp |= b
                    stack.append(v)
                elif colour[v] == colour[u]:
                    bip = False
        if bip:
            return False
        rem &= ~comp
    return True

def bell(n):
    B = [[0] * (n + 1) for _ in range(n + 1)]
    B[0][0] = 1
    for i in range(1, n + 1):
        B[i][0] = B[i - 1][i - 1]
        for j in range(1, i + 1):
            B[i][j] = B[i][j - 1] + B[i - 1][j - 1]
    return B[n][0]

if __name__ == "__main__":
    hi = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    print(f"{'n':>2} {'2^m':>10} {'|ex(H_n)|':>10} {'B_n':>8} {'n^(n-2)-n!/2':>13} {'ratio':>8}")
    for n in range(2, hi + 1):
        E, m, tris = setup(n)
        cnt = 0
        for mask in range(1 << m):
            if extreme(mask, m, tris):
                cnt += 1
        lb = n ** (n - 2) - math.factorial(n) // 2
        print(f"{n:>2} {1<<m:>10} {cnt:>10} {bell(n):>8} {lb:>13} {cnt/(1<<m):>8.4f}")
        sys.stdout.flush()
