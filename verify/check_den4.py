from fractions import Fraction as F
from itertools import combinations
from crosscheck import rank
n=6
E=list(combinations(range(n),2)); idx={e:t for t,e in enumerate(E)}; m=len(E)
d={}
vals=['1/4','3/4','1/4','3/4','3/4','1/2','1/2','1/2','1','1','1','1','1','1','1']
for e,v in zip(E,vals): d[e]=F(v)
def D(i,j): return d[(min(i,j),max(i,j))]
# metric check
ok=all(D(a,b)<=D(a,c)+D(c,b) for a,b,c in __import__('itertools').permutations(range(n),3))
print("is a metric:", ok, " all in [0,1]:", all(0<=x<=1 for x in d.values()))
# tight constraints
rows=[]
for e in E:
    if d[e]==0 or d[e]==1:
        r=[0]*m; r[idx[e]]=1; rows.append(r)
for (i,j,k) in combinations(range(n),3):
    for (a,b,c) in ((i,j,k),(j,i,k),(k,i,j)):
        if D(b,c)==D(a,b)+D(a,c):
            r=[0]*m
            r[idx[(min(b,c),max(b,c))]]+=1
            r[idx[(min(a,b),max(a,b))]]-=1
            r[idx[(min(a,c),max(a,c))]]-=1
            rows.append(r)
print("rank of tight constraints =",rank(rows,m),"of m =",m,"-> extreme:",rank(rows,m)==m)
print("denominator =", 4)
print({str(e):str(v) for e,v in d.items() if v!=1})
