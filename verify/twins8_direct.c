#include <stdio.h>
#include <stdint.h>
int main(){int PA[28],PB[28],m=0;
 for(int a=0;a<8;a++)for(int b=a+1;b<8;b++){PA[m]=a;PB[m]=b;m++;}
 unsigned long long tw=0;
 for(uint64_t mask=0;mask< (1ULL<<28);mask++){
   int adj[8]={0};
   for(int i=0;i<m;i++) if(mask>>i&1){adj[PA[i]]|=1<<PB[i];adj[PB[i]]|=1<<PA[i];}
   int t=0;
   for(int a=0;a<8&&!t;a++)for(int b=a+1;b<8&&!t;b++)
     if((adj[a]>>b)&1){int mk=~((1<<a)|(1<<b))&0xff; if((adj[a]&mk)==(adj[b]&mk)) t=1;}
   if(t) tw++;
 }
 printf("twin-carrying half-one metrics at n=8: %llu\n",tw);
 return 0;}
