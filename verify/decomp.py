"""
Audit of Section 5 (upper-half decomposition).

For a half-one metric d, the perturbations preserving all tight constraints are
   eps -> d + sum_kappa eps_kappa * eta_kappa,
one free parameter per BIPARTITE component kappa of Gamma_d (isolated nodes
included: an isolated node is a bipartite component).  eta_kappa = +-1 on the
nodes of kappa (2-colouring), 0 elsewhere.

The feasible set F = {eps : d + sum eps_kappa eta_kappa in Mbar_n} is cut out by
  (box)   |eps_kappa| <= 1/2                       for each kappa
  (tri)   s_u eps_{c(u)} - s_v eps_{c(v)} - s_w eps_{c(w)} <= 1/2
          for every triangle with ALL THREE edges half, each choice of long side.

The proof of Theorem 5.6 treats the components as independent, i.e. asserts
F = prod_kappa [a_kappa, b_kappa].  We test that.
"""
from itertools import combinations, product
from fractions import Fraction
import sys

def setup(n):
    E = list(combinations(range(n), 2))
    idx = {e: t for t, e in enumerate(E)}
    m = len(E)
    tris = []          # (u,v,w) : u,v short (share apex), w long
    allt = []          # (a,b,c) unordered edge index triples of each 3-subset
    for (i, j, k) in combinations(range(n), 3):
        for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
            tris.append((idx[(min(a,b),max(a,b))], idx[(min(a,c),max(a,c))],
                         idx[(min(b,c),max(b,c))]))
        allt.append((idx[(i,j)], idx[(i,k)], idx[(j,k)]))
    return E, m, tris, allt

def gamma_adj(mask, m, tris):
    adj = [0]*m
    for (u, v, w) in tris:
        if (mask>>u)&1 and (mask>>v)&1 and not (mask>>w)&1:
            adj[u] |= 1<<v
            adj[v] |= 1<<u
    return adj

def components(mask, m, adj):
    """Return list of dicts node->sign(+-1) for each component; second value
    True if bipartite."""
    comps = []
    rem = mask
    while rem:
        s = (rem & -rem).bit_length()-1
        sign = {s: 1}
        stack=[s]; comp = 1<<s; bip=True
        while stack:
            u=stack.pop(); a=adj[u]
            while a:
                b=a&-a; v=b.bit_length()-1; a^=b
                if not (comp>>v)&1:
                    sign[v] = -sign[u]; comp |= b; stack.append(v)
                elif sign[v]==sign[u]:
                    bip=False
        comps.append((sign, bip))
        rem &= ~comp
    return comps

def is_metric(vals, allt):
    """vals: list of Fractions, one per edge. Check 0<=d<=1 and triangle ineqs."""
    for x in vals:
        if x < 0 or x > 1:
            return False
    for (a, b, c) in allt:
        x, y, z = vals[a], vals[b], vals[c]
        if x > y+z or y > x+z or z > x+y:
            return False
    return True

def analyse(n, mask, merge_isolated=True, verbose=False):
    E, m, tris, allt = setup(n)
    adj = gamma_adj(mask, m, tris)
    comps = components(mask, m, adj)
    bipc = [sign for (sign, bip) in comps if bip]
    if not bipc:
        return None                       # d is extreme
    # component index per node
    if merge_isolated:
        iso = {}
        nont = []
        for sign in bipc:
            if len(sign) == 1:
                iso.update(sign)
            else:
                nont.append(sign)
        groups = nont + ([iso] if iso else [])
    else:
        groups = bipc
    N = len(groups)
    cidx = {}
    sgn = {}
    for g, sign in enumerate(groups):
        for u, s in sign.items():
            cidx[u] = g
            sgn[u] = s
    half = [t for t in range(m) if (mask>>t)&1]

    # component-LOCAL ranges (the paper's per-component analysis)
    local = []
    for g in range(N):
        lo, hi = Fraction(-1,2), Fraction(1,2)
        for (a, b, c) in allt:
            if all((mask>>t)&1 for t in (a,b,c)):
                if not all(cidx.get(t,-1)==g for t in (a,b,c)):
                    continue                       # cross-component: ignored
                for (u,v,w) in ((a,b,c),(b,a,c),(c,a,b)):
                    k = sgn[u]-sgn[v]-sgn[w]
                    if k > 0:
                        hi = min(hi, Fraction(1,2*k))
                    elif k < 0:
                        lo = max(lo, Fraction(1,2*k))
        local.append((lo, hi))

    # true feasible corner test
    bad = []
    for choice in product(*[(lo,hi) for (lo,hi) in local]):
        vals = []
        for t in range(m):
            if (mask>>t)&1:
                if t in cidx:
                    vals.append(Fraction(1,2) + sgn[t]*choice[cidx[t]])
                else:
                    vals.append(Fraction(1,2))     # rigid component: no motion
            else:
                vals.append(Fraction(1))
        if not is_metric(vals, allt):
            bad.append((choice, vals))
    return dict(N=N, local=local, ncorner=2**N, bad=bad, half=half,
                cidx=cidx, sgn=sgn, E=E, m=m, allt=allt, mask=mask)

if __name__ == "__main__":
    for n in (4, 5, 6):
        E, m, tris, allt = setup(n)
        tot = 0; failed = 0; first = None
        for mask in range(1<<m):
            r = analyse(n, mask)
            if r is None:
                continue
            tot += 1
            if r["bad"]:
                failed += 1
                if first is None:
                    first = (mask, r)
        print(f"n={n}: {tot} non-extreme half-one metrics; "
              f"{failed} for which the independent-corner construction "
              f"produces a NON-METRIC")
        if first:
            mask, r = first
            print("   first failure: half edges =",
                  [E[t] for t in range(m) if (mask>>t)&1])
            print("   components:", r["N"], " local ranges:", r["local"])
            print("   bad corner eps =", r["bad"][0][0],
                  " -> d =", [str(x) for x in r["bad"][0][1]])
        sys.stdout.flush()
