#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define N 8
static int PA[28],PB[28],PIDX[N][N];
int main(int argc,char**argv){
  int part=atoi(argv[1]), nparts=atoi(argv[2]);
  int m=0; for(int a=0;a<N;a++)for(int b=a+1;b<N;b++){PA[m]=a;PB[m]=b;PIDX[a][b]=PIDX[b][a]=m;m++;}
  uint64_t total=0;
  uint64_t lo=((uint64_t)1<<m)/nparts*part;
  uint64_t hi=(part==nparts-1)?((uint64_t)1<<m):((uint64_t)1<<m)/nparts*(part+1);
  for(uint64_t mask=lo;mask<hi;mask++){
    int adj[N]={0};
    int E[28],k=0;
    for(int i=0;i<m;i++) if(mask>>i&1){adj[PA[i]]|=1<<PB[i]; adj[PB[i]]|=1<<PA[i]; E[k++]=i;}
    /* gamma adjacency as bitmask over k nodes */
    uint32_t g[28]={0};
    for(int x=0;x<k;x++){
      int a=PA[E[x]],b=PB[E[x]];
      for(int y=x+1;y<k;y++){
        int c=PA[E[y]],d=PB[E[y]];
        int u=-1,p=-1,q=-1;
        if(a==c){u=a;p=b;q=d;} else if(a==d){u=a;p=b;q=c;}
        else if(b==c){u=b;p=a;q=d;} else if(b==d){u=b;p=a;q=c;}
        if(u<0) continue;
        if(!((adj[p]>>q)&1)){ g[x]|=1u<<y; g[y]|=1u<<x; }
      }
    }
    /* every component non-bipartite */
    uint32_t seen=0; int ok=1;
    for(int s=0;s<k&&ok;s++){
      if(seen>>s&1) continue;
      uint32_t c0=1u<<s,c1=0,frontier=1u<<s,cur=0; seen|=1u<<s;
      int bip=1;
      while(frontier){
        uint32_t nxt=0;
        for(uint32_t f=frontier;f;f&=f-1){
          int v=__builtin_ctz(f);
          uint32_t nb=g[v];
          uint32_t same=(c0>>v&1)?c0:c1;
          if(nb&same){bip=0;}
          uint32_t newn=nb&~seen;
          nxt|=newn;
          if(c0>>v&1) c1|=newn; else c0|=newn;
        }
        seen|=nxt; frontier=nxt; (void)cur;
      }
      if(bip) ok=0;
    }
    if(ok) total++;
  }
  printf("%llu\n",(unsigned long long)total);
  return 0;
}
