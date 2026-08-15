from itertools import combinations
from fractions import Fraction as Fr
from neighbors import setup, gamma_edges, feasible_interval, den
from fast import setup as fsetup, extreme
from crosscheck import rank

def caps(n, mask, maxtrees=None):
    E,m,tris,allt=setup(n)
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
    out=set()
    for cm in comps:
        cs=set(cm)
        ce=list({(min(u,v),max(u,v)) for (u,v,w) in ge if u in cs and v in cs})
        cnt=0
        for sub in combinations(ce, len(cm)-1):
            par={u:u for u in cm}
            def find(x):
                while par[x]!=x: par[x]=par[par[x]]; x=par[x]
                return x
            ok=True
            for (u,v) in sub:
                ru,rv=find(u),find(v)
                if ru==rv: ok=False; break
                par[ru]=rv
            if not ok: continue
            cnt+=1
            if maxtrees and cnt>maxtrees: break
            tadj={u:[] for u in cm}
            for (u,v) in sub: tadj[u].append(v); tadj[v].append(u)
            col={cm[0]:1}; st=[cm[0]]
            while st:
                u=st.pop()
                for v in tadj[u]:
                    if v not in col: col[v]=-col[u]; st.append(v)
            eta=[0]*m
            for u in cm: eta[u]=col[u]
            lo,hi=feasible_interval(mask,m,allt,eta)
            for eps in (lo,hi):
                if eps==0: continue
                vals=[(Fr(1,2) if (mask>>t)&1 else Fr(1))+eta[t]*eps for t in range(m)]
                out.add(den(vals))
    return out, len(comps)

# minimality: exhaustive n=4,5 ; targeted n=6
for n in (4,5):
    E,m,tris=fsetup(n)
    seen=set()
    for mask in range(1<<m):
        if not extreme(mask,m,tris): continue
        s,nc=caps(n,mask)
        seen|=s
    print(f"n={n}: all neighbour denominators over ALL extreme half-ones and ALL spanning trees: {sorted(seen)}")

# article 1's own n=7 witness
n=7
E,m,tris,allt=setup(n); idx={e:t for t,e in enumerate(E)}
pairs=[(0,4),(0,6),(1,3),(1,4),(2,4),(2,6),(4,5),(4,6),(5,6)]
mask=0
for e in pairs: mask|=1<<idx[e]
_,_,ftris=fsetup(n)
print("\narticle 1 n=7 witness: extreme =", extreme(mask,m,ftris))
s,nc=caps(n,mask)
print("   components:", nc, " neighbour denominators:", sorted(s))
