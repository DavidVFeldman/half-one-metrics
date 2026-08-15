"""
Proposed THEOREM (replacing Conjecture 4.2): the proportion of half-one metrics on n
points that are extreme tends to 1, exponentially fast.

Proof mechanism, for d random half-one with half-length graph G ~ G(n,1/2):
  (1) [claw] an induced claw in G at center i with leaves j,k,l gives the triangle
      [i,j],[i,k],[i,l] in Gamma_d  (each pair adjacent since the connecting side
      {j,k},{k,l},{j,l} is unital);
  (2) [local] for every i and j,k in N_G(i): [i,j],[i,k] lie in one Gamma-component
      (directly adjacent if {j,k} unital; else any l with {i,l} in G, {j,l},{k,l}
      unital gives a 2-path; such l fails with prob (7/8)^{n-3});
  (3) [global] G connected + (2) => all of Gamma_d is one component
      (line graph of a connected graph is connected).
  (1)+(3): the unique component contains an odd cycle => d extreme.

This script measures, for sampled random half-one metrics:
  P(extreme), P(Gamma connected), P(Gamma connected AND has odd cycle),
  P(each sufficient event), and confirms
  {connected & odd cycle} subset {extreme}   (must be 0 exceptions).
"""
import random, sys
from itertools import combinations
from fast import setup, extreme

def gamma_components(mask, m, tris):
    adj=[0]*m
    for (u,v,w) in tris:
        if (mask>>u)&1 and (mask>>v)&1 and not (mask>>w)&1:
            adj[u]|=1<<v; adj[v]|=1<<u
    comps=[]; rem=mask
    while rem:
        s=(rem&-rem).bit_length()-1
        col={s:0}; st=[s]; comp=1<<s; bip=True
        while st:
            u=st.pop(); a=adj[u]
            while a:
                b=a&-a; v=b.bit_length()-1; a^=b
                if not (comp>>v)&1: col[v]=1-col[u]; comp|=b; st.append(v)
                elif col[v]==col[u]: bip=False
        comps.append((comp,bip)); rem&=~comp
    return comps

def run(n, N, seed):
    E,m,tris=setup(n)
    idx={e:t for t,e in enumerate(E)}
    random.seed(seed)
    cnt=dict(ext=0, conn=0, connodd=0, claw=0, viol=0, empty=0)
    for _ in range(N):
        mask=random.getrandbits(m)
        ex=extreme(mask,m,tris)
        if ex: cnt['ext']+=1
        comps=gamma_components(mask,m,tris)
        nedges=bin(mask).count('1')
        if nedges==0:
            cnt['empty']+=1
            continue
        conn=(len(comps)==1)
        odd=conn and not comps[0][1]
        if conn: cnt['conn']+=1
        if odd:
            cnt['connodd']+=1
            if not ex: cnt['viol']+=1     # must never happen
        # induced claw present?
        G=[[False]*n for _ in range(n)]
        for e,t in idx.items():
            if (mask>>t)&1: G[e[0]][e[1]]=G[e[1]][e[0]]=True
        found=False
        for i in range(n):
            nb=[j for j in range(n) if G[i][j]]
            if len(nb)<3: continue
            for (a,b,c) in combinations(nb,3):
                if not G[a][b] and not G[a][c] and not G[b][c]:
                    found=True; break
            if found: break
        if found: cnt['claw']+=1
    return cnt

if __name__=="__main__":
    print(f"{'n':>3} {'P(extreme)':>10} {'P(conn)':>8} {'P(conn&odd)':>11} {'P(claw)':>8} {'violations':>10}")
    for n,N in ((5,4000),(6,4000),(7,4000),(8,3000),(9,2000),(10,1500),(12,800),(14,500)):
        c=run(n,N,101+n)
        print(f"{n:>3} {c['ext']/N:>10.4f} {c['conn']/N:>8.4f} {c['connodd']/N:>11.4f} "
              f"{c['claw']/N:>8.4f} {c['viol']:>10}")
        sys.stdout.flush()
