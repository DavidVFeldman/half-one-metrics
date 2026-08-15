#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static uint64_t s0=0x9E3779B97F4A7C15ULL,s1=0xBF58476D1CE4E5B9ULL;
static inline uint64_t rnd(){uint64_t x=s0;uint64_t y=s1;s0=y;x^=x<<23;s1=x^y^(x>>17)^(y>>26);return s1+y;}
#define MAXN 24
int main(int argc,char**argv){
  int n=atoi(argv[1]); long long N=atoll(argv[2]); s0^=atoll(argv[3])*0x9E3779B97F4A7C15ULL; for(int i=0;i<20;i++) rnd();
  int PA[MAXN*MAXN],PB[MAXN*MAXN],m=0;
  for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){PA[m]=a;PB[m]=b;m++;}
  long long nonext=0, isofail=0, othfail=0;
  int E[MAXN*MAXN];
  static uint64_t g[MAXN*MAXN][ (MAXN*MAXN)/64+1 ];
  for(long long it=0;it<N;it++){
    uint32_t adj[MAXN]; for(int i=0;i<n;i++) adj[i]=0;
    int k=0;
    for(int i=0;i<m;i++){ if(rnd()&1){adj[PA[i]]|=1u<<PB[i];adj[PB[i]]|=1u<<PA[i];E[k++]=i;} }
    int W=(k+63)/64; if(W==0) W=1;
    for(int x=0;x<k;x++) for(int w=0;w<W;w++) g[x][w]=0;
    int deg[MAXN*MAXN]; for(int x=0;x<k;x++) deg[x]=0;
    for(int x=0;x<k;x++){int a=PA[E[x]],b=PB[E[x]];
      for(int y=x+1;y<k;y++){int c=PA[E[y]],d=PB[E[y]];int u=-1,p=0,q=0;
        if(a==c){u=a;p=b;q=d;} else if(a==d){u=a;p=b;q=c;} else if(b==c){u=b;p=a;q=d;} else if(b==d){u=b;p=a;q=c;}
        if(u<0) continue;
        if(!((adj[p]>>q)&1)){ g[x][y>>6]|=1ULL<<(y&63); g[y][x>>6]|=1ULL<<(x&63); deg[x]++;deg[y]++; }
      }}
    int iso=0; for(int x=0;x<k;x++) if(deg[x]==0){iso=1;break;}
    /* bipartite check per component */
    static uint64_t seen[(MAXN*MAXN)/64+1],c0[(MAXN*MAXN)/64+1],c1[(MAXN*MAXN)/64+1],fr[(MAXN*MAXN)/64+1],nx[(MAXN*MAXN)/64+1];
    for(int w=0;w<W;w++){seen[w]=0;c0[w]=0;c1[w]=0;}
    int ok=1;
    for(int s=0;s<k&&ok;s++){
      if(seen[s>>6]>>(s&63)&1) continue;
      for(int w=0;w<W;w++){fr[w]=0;}
      fr[s>>6]|=1ULL<<(s&63); seen[s>>6]|=1ULL<<(s&63); c0[s>>6]|=1ULL<<(s&63);
      int bip=1,any=1;
      while(any){
        any=0; for(int w=0;w<W;w++) nx[w]=0;
        for(int w=0;w<W;w++){ uint64_t f=fr[w];
          while(f){ int v=(w<<6)+__builtin_ctzll(f); f&=f-1;
            int inc0=(c0[v>>6]>>(v&63))&1;
            for(int z=0;z<W;z++){
              uint64_t nb=g[v][z];
              uint64_t same= inc0? c0[z]:c1[z];
              if(nb&same) bip=0;
              uint64_t nn=nb&~seen[z];
              nx[z]|=nn;
              if(inc0) c1[z]|=nn; else c0[z]|=nn;
            }
          }}
        for(int w=0;w<W;w++){ if(nx[w]){any=1;} seen[w]|=nx[w]; fr[w]=nx[w]; }
      }
      if(bip) ok=0;
    }
    if(!ok){ nonext++; if(iso) isofail++; else othfail++; }
  }
  printf("n=%d N=%lld deficit=%.8f iso_share=%.4f\n",n,N,(double)nonext/N,nonext?(double)isofail/nonext:0.0);
  return 0;
}
