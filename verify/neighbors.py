"""
Audit of Section 6 (neighbours of extreme half-one metrics).

For an extreme half-one d, a spanning tree tau of a component kappa of Gamma_d
gives the sign vector eta (+-1 on kappa via the 2-colouring of tau, 0 elsewhere).
We compute EXACTLY the set {eps : d + eps*eta in Mbar_n}, compare with the
criterion of Theorem 6.3 / Corollary 6.4, and record the denominators of the
endpoint metrics.
"""
from itertools import combinations
from fractions import Fraction
import random, sys
from fast import setup as fsetup

def setup(n):
    E = list(combinations(range(n), 2))
    idx = {e: t for t, e in enumerate(E)}
    m = len(E)
    tris, allt = [], []
    for (i, j, k) in combinations(range(n), 3):
        for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
            tris.append((idx[(min(a,b),max(a,b))], idx[(min(a,c),max(a,c))],
                         idx[(min(b,c),max(b,c))]))
        allt.append((idx[(i,j)], idx[(i,k)], idx[(j,k)]))
    return E, m, tris, allt

def gamma_edges(mask, tris):
    return [(u, v, w) for (u, v, w) in tris
            if (mask>>u)&1 and (mask>>v)&1 and not (mask>>w)&1]

def feasible_interval(mask, m, allt, eta):
    """exact [lo,hi] for which d + eps*eta is in Mbar_n (d half-one by mask)."""
    lo, hi = Fraction(-10), Fraction(10)
    def clip(coef, rhs):          # coef*eps <= rhs
        nonlocal lo, hi
        if coef > 0:   return None if False else _hi(Fraction(rhs, 1)/coef)
        if coef < 0:   return _lo(Fraction(rhs, 1)/coef)
        return None
    def _hi(v):
        nonlocal hi
        hi = min(hi, v)
    def _lo(v):
        nonlocal lo, hi
        lo = max(lo, v)
    base = [Fraction(1,2) if (mask>>t)&1 else Fraction(1) for t in range(m)]
    # box 0 <= d <= 1
    for t in range(m):
        clip(eta[t], 1 - base[t])          # base + eta*eps <= 1
        clip(-eta[t], base[t])             # -(base+eta*eps) <= 0
    # triangle inequalities
    for (a, b, c) in allt:
        for (u, v, w) in ((a,b,c),(b,a,c),(c,a,b)):
            # base_u + eta_u e <= base_v+base_w + (eta_v+eta_w) e
            coef = eta[u]-eta[v]-eta[w]
            rhs = base[v]+base[w]-base[u]
            clip(coef, rhs)
    return lo, hi

def den(vals):
    from math import lcm
    d = 1
    for x in vals:
        d = lcm(d, x.denominator)
    return d

def run(n, sample=None, seed=1):
    E, m, tris, allt = setup(n)
    _, _, ftris = fsetup(n)[0], fsetup(n)[1], fsetup(n)[2]
    from fast import extreme
    masks = range(1<<m)
    if sample:
        random.seed(seed)
        masks = [random.getrandbits(m) for _ in range(sample)]
    stats = {}
    mismatch = 0
    examples = {}
    for mask in masks:
        if not extreme(mask, m, ftris):
            continue
        ge = gamma_edges(mask, tris)
        adj = {}
        for (u, v, w) in ge:
            adj.setdefault(u, set()).add(v)
            adj.setdefault(v, set()).add(u)
        nodes = [t for t in range(m) if (mask>>t)&1]
        # components
        seen = set(); comps = []
        for s in nodes:
            if s in seen: continue
            st=[s]; seen.add(s); cm=[s]
            while st:
                u=st.pop()
                for v in adj.get(u,()):
                    if v not in seen:
                        seen.add(v); cm.append(v); st.append(v)
            comps.append(cm)
        ncomp = len(comps)
        for cm in comps:
            cs = set(cm)
            # enumerate spanning trees of the component by brute force over
            # edge subsets of size |cm|-1 (components are small)
            cedges = [(u,v) for (u,v,w) in ge if u in cs and v in cs]
            cedges = list({(min(u,v),max(u,v)) for (u,v) in cedges})
            k = len(cm)-1
            if len(cedges) > 14: continue
            for sub in combinations(cedges, k):
                # is it a spanning tree (connected, k edges, no cycle)?
                par = {u:u for u in cm}
                def find(x):
                    while par[x]!=x: par[x]=par[par[x]]; x=par[x]
                    return x
                ok=True
                for (u,v) in sub:
                    ru,rv=find(u),find(v)
                    if ru==rv: ok=False; break
                    par[ru]=rv
                if not ok: continue
                # 2-colour
                tadj={u:[] for u in cm}
                for (u,v) in sub: tadj[u].append(v); tadj[v].append(u)
                col={cm[0]:1}; st=[cm[0]]
                while st:
                    u=st.pop()
                    for v in tadj[u]:
                        if v not in col: col[v]=-col[u]; st.append(v)
                eta=[0]*m
                for u in cm: eta[u]=col[u]
                lo,hi = feasible_interval(mask, m, allt, eta)
                # criterion: tau^C = component edges not in tau
                pos = neg = False
                for (u,v) in cedges:
                    if (u,v) in sub: continue
                    if col[u]==1 and col[v]==1: pos=True
                    if col[u]==-1 and col[v]==-1: neg=True
                pred_neighbor = not (pos and neg)
                actual_neighbor = (lo < 0 or hi > 0)
                if pred_neighbor != actual_neighbor:
                    mismatch += 1
                    examples.setdefault("criterion", (mask, cm, sub, lo, hi, pos, neg))
                for eps in (lo, hi):
                    if eps == 0: continue
                    vals=[ (Fraction(1,2) if (mask>>t)&1 else Fraction(1)) + eta[t]*eps
                           for t in range(m)]
                    q = den(vals)
                    key=(ncomp==1, q)
                    stats[key]=stats.get(key,0)+1
                    if ncomp>1 and q not in (1,2,3,6):
                        examples.setdefault(("den",q), (mask, cm, sub, eps, vals))
                    if ncomp==1 and q not in (1,3):
                        examples.setdefault(("den1",q), (mask, cm, sub, eps, vals))
    return stats, mismatch, examples, E

if __name__ == "__main__":
    for n in (4,5,6):
        stats, mis, ex, E = run(n)
        print(f"n={n}  criterion mismatches = {mis}")
        conn = {q:c for (c1,q),c in stats.items() if c1}
        disc = {q:c for (c1,q),c in stats.items() if not c1}
        print(f"   Gamma_d CONNECTED  : neighbour denominators {dict(sorted(conn.items()))}")
        print(f"   Gamma_d DISCONNECTED: neighbour denominators {dict(sorted(disc.items()))}")
        for k,v in ex.items():
            if isinstance(k, tuple):
                mask, cm, sub, eps, vals = v
                print(f"   !! {k}: half edges {[E[t] for t in range(len(E)) if (mask>>t)&1]}")
                print(f"      component {[E[t] for t in cm]} eps={eps}")
                print(f"      d_tau = {[str(x) for x in vals]}")
        sys.stdout.flush()
