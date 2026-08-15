"""Capture and exactly certify any n=7 vertex with denominator outside article 1's list."""
import numpy as np
from fractions import Fraction as Fr
from itertools import combinations
from lp import build
from scipy.optimize import linprog
from crosscheck import rank
def denom(x,maxq=60,tol=2e-7):
    for q in range(1,maxq+1):
        if np.max(np.abs(q*x-np.round(q*x)))<tol*max(1,q): return q
    return None
n=7; E,m,A=build(n); b=np.zeros(A.shape[0])
idx={e:t for t,e in enumerate(E)}
allt=[(idx[(i,j)],idx[(i,k)],idx[(j,k)]) for (i,j,k) in combinations(range(n),3)]
rng=np.random.default_rng(77); hits={}
for _ in range(6000):
    r=linprog(-rng.normal(size=m),A_ub=A,b_ub=b,bounds=[(0,1)]*m,method="highs")
    q=denom(r.x)
    if q is not None and q not in (1,2,3,4,5,6) and q not in hits:
        vals=[Fr(int(round(q*v)),q) for v in r.x]
        ok=all(0<=v<=1 for v in vals)
        for (a,bb,c) in allt:
            x,y,z=vals[a],vals[bb],vals[c]
            if not (x<=y+z and y<=x+z and z<=x+y): ok=False;break
        rows=[]
        for t in range(m):
            if vals[t]==0 or vals[t]==1:
                rr=[0]*m; rr[t]=1; rows.append(rr)
        for (a,bb,c) in allt:
            for (u,v,w) in ((a,bb,c),(bb,a,c),(c,a,bb)):
                if vals[u]==vals[v]+vals[w]:
                    rr=[0]*m; rr[u]+=1; rr[v]-=1; rr[w]-=1; rows.append(rr)
        rk=rank(rows,m)
        hits[q]=(ok,rk,vals)
        print(f"denominator {q}: exact metric={ok}, rank={rk} of {m}, extreme={rk==m}")
        print("   values:", {str(E[t]):str(vals[t]) for t in range(m) if vals[t]!=1})
if not hits: print("no vertex outside {1,...,6} found at n=7")
