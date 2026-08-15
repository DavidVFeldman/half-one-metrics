"""Random search: denominators of neighbours d_tau when Gamma_d is disconnected."""
import random, sys
from fractions import Fraction as Fr
from neighbors import setup, gamma_edges, feasible_interval, den
from fast import setup as fsetup, extreme
for n in (6,7):
    E,m,tris,allt = setup(n); _,_,ftris = fsetup(n)
    random.seed(99+n); spec={}; ex6=None
    for _ in range(40000):
        mask=random.getrandbits(m)
        if not extreme(mask,m,ftris): continue
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
        if len(comps)<2: continue
        for cm in comps:
            cs=set(cm)
            ce=list({(min(u,v),max(u,v)) for (u,v,w) in ge if u in cs and v in cs})
            if not ce: continue
            for _ in range(6):                       # random spanning trees
                random.shuffle(ce)
                par={u:u for u in cm}
                def find(x):
                    while par[x]!=x: par[x]=par[par[x]]; x=par[x]
                    return x
                sub=[]
                for (u,v) in ce:
                    ru,rv=find(u),find(v)
                    if ru!=rv: par[ru]=rv; sub.append((u,v))
                if len(sub)!=len(cm)-1: continue
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
                    q=den(vals); spec[q]=spec.get(q,0)+1
                    if q==6 and ex6 is None: ex6=(mask,eps,vals)
    print(f"n={n}: neighbour denominators (Gamma_d disconnected) {dict(sorted(spec.items()))}")
    if ex6:
        mask,eps,vals=ex6
        print("   denominator-6 example half edges:",[E[t] for t in range(m) if (mask>>t)&1])
        print("   d_tau =",[str(x) for x in vals])
    sys.stdout.flush()
