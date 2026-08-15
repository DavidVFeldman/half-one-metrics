"""
Independent verification of the enumerative claims of article 3
(ultrametrics, partition chains, iterated cycle structures).

Everything is exact integer arithmetic.  ICS are counted three ways:
  (a) by brute-force construction of towers for small n,
  (b) by the matrix identity N(n,k+1) = (Stm^k)(n,1),
  (c) by the fibration over augmented chains of Pi_n.
"""
from itertools import combinations
from math import factorial
from functools import lru_cache
import sys

# ---------- Stirling numbers ----------
def stirling1(N):
    """unsigned first kind: St[n][k]"""
    S = [[0]*(N+1) for _ in range(N+1)]
    S[0][0] = 1
    for n in range(1, N+1):
        for k in range(1, n+1):
            S[n][k] = S[n-1][k-1] + (n-1)*S[n-1][k]
    return S

def stirling2(N):
    S = [[0]*(N+1) for _ in range(N+1)]
    S[0][0] = 1
    for n in range(1, N+1):
        for k in range(1, n+1):
            S[n][k] = S[n-1][k-1] + k*S[n-1][k]
    return S

def bell(N):
    S2 = stirling2(N)
    return [sum(S2[n][k] for k in range(0, n+1)) for n in range(N+1)]

# ---------- (a) brute force towers ----------
def perms_with_cycles(elts):
    """yield (list_of_cycles) for every permutation of elts, as a partition into
    cyclically ordered blocks; returns list of tuples of frozensets (the cycles)."""
    elts = list(elts)
    if not elts:
        yield []
        return
    # choose the block containing elts[0], then a cyclic order on it
    first = elts[0]
    rest = elts[1:]
    for r in range(len(rest)+1):
        for comb in combinations(rest, r):
            block = (first,) + comb
            ncyc = factorial(len(block)-1)          # cyclic orders on the block
            remaining = [e for e in rest if e not in comb]
            for tail in perms_with_cycles(remaining):
                for _ in range(ncyc):
                    yield [frozenset(block)] + tail

def count_ics_bruteforce(n):
    """count ICS on n points by explicit tower construction; returns dict length->count"""
    from collections import defaultdict
    out = defaultdict(int)
    def rec(level_set, m):
        # level_set: current cycle set (a tuple of hashable items)
        if len(level_set) == 1 and m >= 2:
            out[m] += 1
            return
        if len(level_set) == 1:
            return
        for cycles in perms_with_cycles(level_set):
            if len(cycles) == len(level_set):
                continue                      # trivial permutation
            rec(tuple(sorted(cycles, key=lambda s: sorted(map(str, s)))), m+1)
    if n == 1:
        return {1: 1}
    rec(tuple(range(n)), 1)
    return dict(out)

# ---------- (b) matrix identity ----------
def matmul(A, B, N):
    C = [[0]*(N+1) for _ in range(N+1)]
    for i in range(N+1):
        Ai = A[i]
        for k in range(N+1):
            if Ai[k]:
                a = Ai[k]; Bk = B[k]
                for j in range(N+1):
                    if Bk[j]: C[i][j] += a*Bk[j]
    return C

def N_matrix(N):
    St = stirling1(N)
    Stm = [[St[i][j] if i > j else 0 for j in range(N+1)] for i in range(N+1)]
    return Stm

# ---------- (c) fibration over augmented chains ----------
def partitions_of(s):
    s = list(s)
    if not s:
        yield []
        return
    first, rest = s[0], s[1:]
    for r in range(len(rest)+1):
        for comb in combinations(rest, r):
            block = frozenset((first,)+comb)
            remaining = [e for e in rest if e not in comb]
            for p in partitions_of(remaining):
                yield [block]+p

def refines(P, Q):
    """P <= Q : every block of P inside some block of Q"""
    return all(any(b <= c for c in Q) for b in P)

def ics_via_chains(n):
    """|ICS(n)| = sum over augmented chains 0<...<1 of prod prod (beta-1)!"""
    pts = list(range(n))
    parts = [tuple(sorted(p, key=lambda b: sorted(b))) for p in partitions_of(pts)]
    zero = tuple(sorted((frozenset([x]) for x in pts), key=lambda b: sorted(b)))
    one = (frozenset(pts),)
    from collections import defaultdict
    total = defaultdict(int)
    def fiber_step(P, Q):
        w = 1
        for B in Q:
            beta = sum(1 for b in P if b <= B)
            w *= factorial(beta-1)
        return w
    def rec(cur, m, w):
        if cur == one:
            total[m] += w
            return
        for Q in parts:
            if Q == cur: continue
            if refines(cur, Q):
                rec(Q, m+1, w*fiber_step(cur, Q))
    if n == 1:
        return {1: 1}
    rec(zero, 1, 1)
    return dict(total)

# ---------- Euler characteristic of Delta(hat Pi_n) ----------
def euler_hatPi(n):
    pts = list(range(n))
    parts = [tuple(sorted(p, key=lambda b: sorted(b))) for p in partitions_of(pts)]
    zero = tuple(sorted((frozenset([x]) for x in pts), key=lambda b: sorted(b)))
    one = (frozenset(pts),)
    inner = [p for p in parts if p != zero and p != one]
    idx = {p: i for i, p in enumerate(inner)}
    below = {p: [q for q in inner if q != p and refines(p, q)] for p in inner}
    chi = 0
    def rec(p, size):
        nonlocal chi
        chi += (-1)**(size-1)          # face of dimension size-1
        for q in below[p]:
            if idx[q] > -1:
                rec(q, size+1)
    for p in inner:
        rec(p, 1)
    return chi

if __name__ == "__main__":
    N = 12
    St = stirling1(N); S2 = stirling2(N); B = bell(N)
    Stm = N_matrix(N)

    # ---- |ICS(n)| three ways
    print("=== |ICS(n)| ===")
    claimed = [None,1,1,5,47,719,16299,513253,21430513,1145710573]
    # (b) matrix
    P = [[1 if i==j else 0 for j in range(N+1)] for i in range(N+1)]
    Nnm = {}
    for k in range(1, N+1):
        P = matmul(P, Stm, N)
        for n in range(1, N+1):
            if P[n][1]: Nnm[(n, k+1)] = P[n][1]
    mat = [None] + [1] + [sum(v for (n_,m_),v in Nnm.items() if n_==n) for n in range(2, N+1)]
    print(f"{'n':>2} {'claimed':>12} {'matrix':>12} {'brute':>12} {'chains':>12} {'odd?':>5}")
    for n in range(1, 8):
        bf = sum(count_ics_bruteforce(n).values()) if n <= 6 else None
        ch = sum(ics_via_chains(n).values()) if n <= 6 else None
        c = claimed[n] if n < len(claimed) else None
        print(f"{n:>2} {str(c):>12} {str(mat[n]):>12} {str(bf):>12} {str(ch):>12} "
              f"{str(mat[n]%2==1):>5}")
    print("   full matrix sequence:", [mat[n] for n in range(1, 10)])
    sys.stdout.flush()

    # ---- recurrence  2|ICS(n)| = sum_k St(n,k)|ICS(k)|
    print("\n=== recurrence 2|ICS(n)| = sum_k St(n,k)|ICS(k)| ===")
    ok = all(2*mat[n] == sum(St[n][k]*mat[k] for k in range(1, n+1))
             for n in range(2, N+1))
    print("   holds for 2<=n<=", N, ":", ok)

    # ---- weighted sum
    print("\n=== Theorem (ics-weight): sum (-1)^(n-m) = 1 ===")
    for n in range(1, 9):
        tot = sum((-1)**(n-m)*v for (n_, m), v in Nnm.items() if n_ == n)
        if n == 1: tot = 1
        print(f"   n={n}: {tot}")

    # ---- N(n,2) = (n-1)!
    print("\n=== N(n,2) = (n-1)! ===")
    print("  ", all(Nnm.get((n,2),0) == factorial(n-1) for n in range(2, N+1)))

    # ---- Lemma bell-stirling
    print("\n=== Lemma (bell-stirling): sum_k (-1)^(n-k) B_k St(n,k) = 1 ===")
    for n in range(1, 10):
        print(f"   n={n}: {sum((-1)**(n-k)*B[k]*St[n][k] for k in range(1, n+1))}")

    # ---- pointed ICS
    print("\n=== Theorem (pointed-ics): sum over ICS+ = B_n - 1, ICS+ (final unmarked) = B_n - 2 ===")
    for n in range(1, 9):
        plus = sum((-1)**(n-m)*(m-1)*v for (n_, m), v in Nnm.items() if n_ == n)
        oplus = sum((-1)**(n-m)*(m-2)*v for (n_, m), v in Nnm.items() if n_ == n)
        print(f"   n={n}: ICS+ = {plus} (B_n-1 = {B[n]-1});  "
              f"ICS(+) = {oplus} (B_n-2 = {B[n]-2})")

    # ---- Euler characteristic
    print("\n=== Theorem (euler-char): chi(Delta(hat Pi_n)) = (-1)^(n-1)(n-1)!+1 ===")
    for n in range(3, 7):
        e = euler_hatPi(n)
        print(f"   n={n}: computed {e}, formula {(-1)**(n-1)*factorial(n-1)+1}")

    # ---- Prop ics-chi and Cor no-wedge
    print("\n=== Prop (ics-chi): sum_{m>=3} (-1)^(m-3) N(n,m) = (n-1)!+(-1)^(n-1) ===")
    for n in range(2, 9):
        s = sum((-1)**(m-3)*v for (n_, m), v in Nnm.items() if n_ == n and m >= 3)
        print(f"   n={n}: computed {s}, formula {factorial(n-1)+(-1)**(n-1)}")
    print("\n=== Cor (no-wedge) at n=4: vertices N(4,3), edges N(4,4) ===")
    print(f"   N(4,3) = {Nnm.get((4,3))}, N(4,4) = {Nnm.get((4,4))}")
