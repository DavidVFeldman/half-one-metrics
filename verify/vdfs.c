/* Vertex census of Mbar_n over the grid (1/L)Z^m via DFS with triangle pruning. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MOD 1000003LL
static int n,m,L;
static int eidx[10][10];
static int tris_at[16][60][2];
static int ntri_at[16];
static long long rows[220][16];
static int nrows;
static long long verts=0, pdv=0, mets=0;
static int d[16];

static long long inv(long long a){long long r=1,e=MOD-2;a%=MOD;while(e){if(e&1)r=r*a%MOD;a=a*a%MOD;e>>=1;}return r;}
static int rank_mod(void){
    int rk=0;
    for(int c=0;c<m&&rk<nrows;c++){
        int p=-1;
        for(int i=rk;i<nrows;i++) if(rows[i][c]%MOD){p=i;break;}
        if(p<0) continue;
        for(int j=0;j<m;j++){long long t=rows[rk][j];rows[rk][j]=rows[p][j];rows[p][j]=t;}
        long long iv=inv(rows[rk][c]);
        for(int j=0;j<m;j++) rows[rk][j]=rows[rk][j]%MOD*iv%MOD;
        for(int i=0;i<nrows;i++) if(i!=rk&&rows[i][c]%MOD){
            long long f=rows[i][c]%MOD;
            for(int j=0;j<m;j++) rows[i][j]=((rows[i][j]-f*rows[rk][j])%MOD+MOD)%MOD;
        }
        rk++;
    }
    return rk;
}
static void build(void){
    int t=0;
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){eidx[i][j]=eidx[j][i]=t;t++;}
    m=t;
    memset(ntri_at,0,sizeof ntri_at);
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) for(int k=j+1;k<n;k++){
        int a=eidx[i][j],b=eidx[i][k],c=eidx[j][k];
        int mx=a>b?(a>c?a:c):(b>c?b:c);
        int o1,o2;
        if(mx==a){o1=b;o2=c;} else if(mx==b){o1=a;o2=c;} else {o1=a;o2=b;}
        tris_at[mx][ntri_at[mx]][0]=o1; tris_at[mx][ntri_at[mx]][1]=o2; ntri_at[mx]++;
    }
}
static void check_vertex(void){
    mets++;
    nrows=0;
    for(int i=0;i<m;i++) if(d[i]==0||d[i]==L){memset(rows[nrows],0,sizeof(long long)*16);rows[nrows][i]=1;nrows++;}
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) for(int k=j+1;k<n;k++){
        int a=eidx[i][j],b=eidx[i][k],c=eidx[j][k];
        int v[3]={a,b,c};
        for(int s=0;s<3;s++){
            int u=v[s],x=v[(s+1)%3],y=v[(s+2)%3];
            if(d[u]==d[x]+d[y]){
                memset(rows[nrows],0,sizeof(long long)*16);
                rows[nrows][u]+=1;
                rows[nrows][x]=(rows[nrows][x]+MOD-1)%MOD;
                rows[nrows][y]=(rows[nrows][y]+MOD-1)%MOD;
                nrows++;
            }
        }
    }
    if(nrows>=m && rank_mod()==m){
        verts++;
        int pos=1;
        for(int i=0;i<m;i++) if(d[i]==0) pos=0;
        if(pos) pdv++;
    }
}
static void dfs(int t){
    if(t==m){check_vertex();return;}
    for(int v=0;v<=L;v++){
        d[t]=v;
        int ok=1;
        for(int q=0;q<ntri_at[t]&&ok;q++){
            int x=tris_at[t][q][0],y=tris_at[t][q][1];
            if(d[t]>d[x]+d[y]||d[x]>d[t]+d[y]||d[y]>d[t]+d[x]) ok=0;
        }
        if(ok) dfs(t+1);
    }
}
int main(int argc,char**argv){
    n=atoi(argv[1]); L=atoi(argv[2]);
    build();
    dfs(0);
    printf("n=%d L=%d : %lld metrics on grid, %lld vertices (%lld positive-definite)\n",n,L,mets,verts,pdv);
    return 0;
}
