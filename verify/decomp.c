/* For every half-one metric on n points (graph G on n vertices), classify:
     EXTREME        every Gamma-component has an odd cycle
     ISO            non-extreme with an isolated Gamma-node  (= true twin pair in G)
     OTHER          non-extreme, no isolated node (some larger bipartite component)
   Also records, among OTHER, the minimum size of a bipartite component.
   Exhaustive over all 2^C(n,2) graphs.                                        */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, m;
static int EA[32], EB[32];
static int eidx[9][9];
/* for each ordered pair of distinct edge slots sharing a vertex: third index */
static int nadj[32];
static int adje[32][64];   /* other edge slot */
static int adjt[32][64];   /* third-pair slot */

static void build(void){
    int t=0;
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){eidx[i][j]=eidx[j][i]=t;EA[t]=i;EB[t]=j;t++;}
    m=t;
    memset(nadj,0,sizeof nadj);
    for(int e=0;e<m;e++) for(int f=0;f<m;f++){
        if(e==f) continue;
        int a=EA[e],b=EB[e],c=EA[f],d=EB[f];
        int shared=-1,x=-1,y=-1;
        if(a==c){shared=a;x=b;y=d;} else if(a==d){shared=a;x=b;y=c;}
        else if(b==c){shared=b;x=a;y=d;} else if(b==d){shared=b;x=a;y=c;}
        else continue;
        adje[e][nadj[e]]=f;
        adjt[e][nadj[e]]=eidx[x][y];
        nadj[e]++;
    }
}

int main(int argc,char**argv){
    n=atoi(argv[1]); build();
    long long total=1LL<<m;
    long long ext=0, iso=0, other=0;
    long long minbip[40]; memset(minbip,0,sizeof minbip);
    int col[32], stack[32];
    for(long long g=0; g<total; g++){
        int bad=0;            /* found bipartite component */
        int hasiso=0;
        int minb=999;
        memset(col,-1,sizeof(int)*m);
        for(int s=0;s<m;s++){
            if(!((g>>s)&1) || col[s]>=0) continue;
            /* BFS the component of s, 2-coloring */
            int sp=0, comp=0, bip=1;
            col[s]=0; stack[sp++]=s;
            while(sp){
                int e=stack[--sp]; comp++;
                for(int q=0;q<nadj[e];q++){
                    int f=adje[e][q];
                    if(!((g>>f)&1)) continue;
                    if((g>>adjt[e][q])&1) continue;   /* third side half: no adjacency */
                    if(col[f]<0){col[f]=1-col[e]; stack[sp++]=f;}
                    else if(col[f]==col[e]) bip=0;
                }
            }
            if(bip){ bad=1; if(comp==1) hasiso=1; if(comp<minb) minb=comp; }
        }
        if(!bad) ext++;
        else if(hasiso) iso++;
        else { other++; if(minb<40) minbip[minb]++; }
    }
    printf("n=%d  total=%lld  extreme=%lld  iso=%lld  other=%lld\n",n,total,ext,iso,other);
    printf("  deficit D = %.6f   iso-share of deficit = %.4f\n",
           (double)(iso+other)/total, iso+other? (double)iso/(iso+other) : 0.0);
    printf("  min bipartite comp size among OTHER:");
    for(int s=0;s<40;s++) if(minbip[s]) printf("  %d:%lld",s,minbip[s]);
    printf("\n");
    return 0;
}
