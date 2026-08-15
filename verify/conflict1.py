"""CONFLICT 1: article 1 Cor.(neighbor-form) says denominator 4 'occurs first at n=7'.
   Article 1 Rem.(denominators) says n=6 vertices already include denominator 4.
   Test: does a denominator-4 NEIGHBOUR of an extreme half-one exist at n=6?"""
from fractions import Fraction as Fr
from itertools import combinations
from neighbors import setup, gamma_edges, feasible_interval, den
from fast import setup as fsetup, extreme
from crosscheck import rank

n=6
E,m,tris,allt = setup(n); _,_,ftris = fsetup(n)
half = [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)]
idx={e:t for t,e in enumerate(E)}
mask=0
for e in half: mask |= 1<<idx[e]
print("base d extreme:", extreme(mask,m,ftris))

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
print("components of Gamma_d:", [[E[t] for t in c] for c in comps])

# equilateral triangles spanning two components
comp_of={}
for i,c in enumerate(comps):
    for t in c: comp_of[t]=i
for (a,b,c) in allt:
    if all((mask>>t)&1 for t in (a,b,c)):
        cs={comp_of[a],comp_of[b],comp_of[c]}
        if len(cs)>1:
            print("  equilateral triangle across components:",
                  [E[a],E[b],E[c]], "components", sorted(cs))

# walk each spanning tree of kappa_1
kappa=comps[0]; cs=set(kappa)
ce=list({(min(u,v),max(u,v)) for (u,v,w) in ge if u in cs and v in cs})
found=[]
for sub in combinations(ce, len(kappa)-1):
    par={u:u for u in kappa}
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    ok=True
    for (u,v) in sub:
        ru,rv=find(u),find(v)
        if ru==rv: ok=False; break
        par[ru]=rv
    if not ok: continue
    tadj={u:[] for u in kappa}
    for (u,v) in sub: tadj[u].append(v); tadj[v].append(u)
    col={kappa[0]:1}; st=[kappa[0]]
    while st:
        u=st.pop()
        for v in tadj[u]:
            if v not in col: col[v]=-col[u]; st.append(v)
    eta=[0]*m
    for u in kappa: eta[u]=col[u]
    lo,hi=feasible_interval(mask,m,allt,eta)
    for eps in (lo,hi):
        if eps==0: continue
        vals=[(Fr(1,2) if (mask>>t)&1 else Fr(1))+eta[t]*eps for t in range(m)]
        if den(vals)==4: found.append((eps,vals,sub))
print("\nnumber of spanning trees of kappa_1 giving a denominator-4 neighbour:", len(found))
eps,vals,sub = found[0]
print("eps* =",eps)
print("d_tau =", {str(E[t]):str(vals[t]) for t in range(m) if vals[t]!=1})
# rank certificate
rows=[]
for t in range(m):
    if vals[t]==0 or vals[t]==1:
        r=[0]*m; r[t]=1; rows.append(r)
for (a,b,c) in allt:
    for (u,v,w) in ((a,b,c),(b,a,c),(c,a,b)):
        if vals[u]==vals[v]+vals[w]:
            r=[0]*m; r[u]+=1; r[v]-=1; r[w]-=1; rows.append(r)
print("rank of active constraints at d_tau:", rank(rows,m), "of", m)
# edge certificate: face F_tau one-dimensional
print("F_tau is the segment eps in", (lo,hi), "-> dimension 1:", lo!=hi)
