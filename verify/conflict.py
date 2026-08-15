"""Article 1, Cor 5.2: 'denominator 4 occurs first at n=7'.
   My audit found denominator-4 neighbours at n=6. Resolve, rigorously."""
from itertools import combinations
from fractions import Fraction as Fr
from neighbors import setup, gamma_edges, feasible_interval, den
from crosscheck import rank

n=6
E,m,tris,allt = setup(n); idx={e:t for t,e in enumerate(E)}
half=[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)]
mask=0
for e in half: mask |= 1<<idx[e]
print("half-length pairs:", half)

ge=gamma_edges(mask,tris)
adj={}
for (u,v,w) in ge: adj.setdefault(u,set()).add(v); adj.setdefault(v,set()).add(u)
nodes=[t for t in range(m) if (mask>>t)&1]
seen=set(); comps=[]
for s in nodes:
    if s in seen: continue
    st=[s]; seen.add(s); cm=[s]
    while st:
        u=st.pop()
        for v in adj.get(u,()):
            if v not in seen: seen.add(v); cm.append(v); st.append(v)
    comps.append(cm)
print("Gamma_d components:")
def oddcycle(cm):
    col={cm[0]:0}; st=[cm[0]]; bip=True
    while st:
        u=st.pop()
        for v in adj.get(u,()):
            if v not in col: col[v]=1-col[u]; st.append(v)
            elif col[v]==col[u]: bip=False
    return not bip
for cm in comps:
    print("   ", [E[t] for t in cm], " contains odd cycle:", oddcycle(cm))
print("d extreme:", all(oddcycle(c) for c in comps), " #components:", len(comps))

# the component of {0,1}
kap=[c for c in comps if idx[(0,1)] in c][0]
cs=set(kap)
ce=list({(min(u,v),max(u,v)) for (u,v,w) in ge if u in cs and v in cs})
print("kappa =", [E[t] for t in kap], " Gamma-edges in kappa:", len(ce))

best=None
for sub in combinations(ce, len(kap)-1):
    par={u:u for u in kap}
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    ok=True
    for (u,v) in sub:
        ru,rv=find(u),find(v)
        if ru==rv: ok=False; break
        par[ru]=rv
    if not ok: continue
    tadj={u:[] for u in kap}
    for (u,v) in sub: tadj[u].append(v); tadj[v].append(u)
    col={kap[0]:1}; st=[kap[0]]
    while st:
        u=st.pop()
        for v in tadj[u]:
            if v not in col: col[v]=-col[u]; st.append(v)
    eta=[0]*m
    for u in kap: eta[u]=col[u]
    lo,hi=feasible_interval(mask,m,allt,eta)
    for eps in (lo,hi):
        if eps==0: continue
        vals=[(Fr(1,2) if (mask>>t)&1 else Fr(1))+eta[t]*eps for t in range(m)]
        if den(vals)==4:
            best=(sub,eta,eps,vals); break
    if best: break

sub,eta,eps,vals=best
print("\nspanning tree of kappa:", [(E[u],E[v]) for (u,v) in sub])
print("cap eps* =", eps)
print("neighbour d_tau:")
for e,v in zip(E,vals):
    if v!=1: print(f"     d{e} = {v}")
rows=[]
for t in range(m):
    if vals[t]==0 or vals[t]==1:
        r=[0]*m; r[t]=1; rows.append(r)
for (a,b,c) in allt:
    for (u,v,w) in ((a,b,c),(b,a,c),(c,a,b)):
        if vals[u]==vals[v]+vals[w]:
            r=[0]*m; r[u]+=1; r[v]-=1; r[w]-=1; rows.append(r)
print("rank of active constraints at d_tau:", rank(rows,m), "of", m)
print("denominator:", den(vals))

# is [d, d_tau] an edge?  motions in F_tau: vanish on U_d, alternate on tau,
# vanish on rigid components -> dimension <= 1, so yes provided other comps rigid.
print("other components rigid:", all(oddcycle(c) for c in comps if c is not kap))

# the equilateral triangle straddling two components
for (a,b,c) in allt:
    if all((mask>>t)&1 for t in (a,b,c)):
        cc={next(i for i,cm in enumerate(comps) if t in cm) for t in (a,b,c)}
        if len(cc)>1:
            print("straddling equilateral triangle:", [E[t] for t in (a,b,c)],
                  "components", sorted(cc))
