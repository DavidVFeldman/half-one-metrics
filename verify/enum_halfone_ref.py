import itertools, sys
from collections import deque

def counts(n):
    P=list(itertools.combinations(range(n),2))
    m=len(P)
    tot=0
    for mask in range(1<<m):
        # G_d edges = half-length pairs
        adjG=[[False]*n for _ in range(n)]
        E=[]
        for i,(a,b) in enumerate(P):
            if mask>>i & 1:
                adjG[a][b]=adjG[b][a]=True; E.append((a,b))
        k=len(E)
        idx={e:i for i,e in enumerate(E)}
        # Gamma_d : nodes = E, {i,j}~{i,k} iff share endpoint and third side NOT in G
        nb=[[] for _ in range(k)]
        for x in range(k):
            for y in range(x+1,k):
                a,b=E[x]; c,e=E[y]
                s=set((a,b))&set((c,e))
                if len(s)!=1: continue
                u=s.pop()
                p=(a if a!=u else b); q=(c if c!=u else e)
                if not adjG[p][q]:
                    nb[x].append(y); nb[y].append(x)
        # every component contains an odd cycle  <=>  no component bipartite
        col=[-1]*k; ok=True
        for s in range(k):
            if col[s]!=-1: continue
            col[s]=0; dq=deque([s]); bip=True
            while dq:
                v=dq.popleft()
                for w in nb[v]:
                    if col[w]==-1: col[w]=col[v]^1; dq.append(w)
                    elif col[w]==col[v]: bip=False
            if bip: ok=False; break
        if ok: tot+=1
    return tot

for n in range(3,8):
    c=counts(n); M=1<<(n*(n-1)//2)
    print(f"n={n}: |ex(H_n)|={c}  of 2^C(n,2)={M}  prop={c/M:.4f}  deficit={1-c/M:.6f}")
