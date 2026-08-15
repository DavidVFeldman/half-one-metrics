/* Count graphs on n vertices containing a true twin pair (adjacent, same
   neighbourhoods elsewhere).  Row-mask method, no BFS. */
#include <stdio.h>
#include <stdlib.h>
static int n,m,eidx[9][9],EA[36],EB[36];
int main(int argc,char**argv){
    n=atoi(argv[1]);
    int t=0;
    for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){eidx[i][j]=eidx[j][i]=t;EA[t]=i;EB[t]=j;t++;}
    m=t;
    long long total=1LL<<m, twin=0;
    for(long long g=0;g<total;g++){
        unsigned row[9]={0};
        long long gg=g;
        for(int e=0;e<m;e++){ if(gg&1){row[EA[e]]|=1u<<EB[e];row[EB[e]]|=1u<<EA[e];} gg>>=1; }
        int has=0;
        for(int e=0;e<m && !has;e++){
            if(!((g>>e)&1)) continue;
            int i=EA[e],j=EB[e];
            unsigned d=(row[i]^row[j]) & ~((1u<<i)|(1u<<j));
            if(!d) has=1;
        }
        twin+=has;
    }
    printf("n=%d graphs-with-true-twin = %lld of %lld\n",n,twin,total);
    return 0;
}
