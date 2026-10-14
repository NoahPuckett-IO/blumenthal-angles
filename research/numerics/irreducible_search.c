// Search for "irreducible" configurations: s>=4 points, max angle <= pi-lam,
// such that for every y, Delta(y) := sum_{r!=y} (2^{k_{Q-y}(r)} - 2^{k_Q(r)}) < 2^{k_Q(y)}.
// usage: red u s iters restarts seed
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXS 32
static double PI, U, LAM, AMAX; static int S;
static unsigned long long rs;
static double rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (rs>>11)*(1.0/9007199254740992.0);}
static double gauss(void){ double a=rnd(),b=rnd(); if(a<1e-300)a=1e-300; return sqrt(-2*log(a))*cos(2*PI*b);}
static int cmpd(const void*a,const void*b){double x=*(const double*)a,y=*(const double*)b;return (x>y)-(x<y);}
static double maxangle(double (*P)[2], int s){ double best=0;
  for(int i=0;i<s;i++){ double a[MAXS]; int m=0;
    for(int j=0;j<s;j++) if(j!=i) a[m++]=atan2(P[j][1]-P[i][1],P[j][0]-P[i][0]);
    for(int x=0;x<m;x++) for(int y=x+1;y<m;y++){ double d=fabs(a[x]-a[y]); if(d>PI)d=2*PI-d; if(d>best)best=d;}}
  return best;}
// k of point i in configuration with point 'skip' removed (skip=-1 none)
static int kof(double (*P)[2], int s, int i, int skip){ double t[MAXS]; int m=0;
  for(int j=0;j<s;j++) if(j!=i && j!=skip){ double a=atan2(P[j][1]-P[i][1],P[j][0]-P[i][0]); t[m++]=fmod(a+2*PI,PI);}
  if(m==0) return 1000; qsort(t,m,sizeof(double),cmpd); int kk=0;
  for(int g=0;g<m;g++){ double gap=(g+1<m?t[g+1]:t[0]+PI)-t[g]; int c=(int)floor(gap/LAM+1e-12)-1; if(c>0)kk+=c;}
  return kk;}
// margin = min_y (2^k(y) - Delta(y)); >0 means irreducible
static double margin(double (*P)[2], long long *Fout){
  double ma=maxangle(P,S); if(ma>AMAX){*Fout=-1; return -1000.0*(ma-AMAX)-100;}
  int k[MAXS]; long long F=0; for(int i=0;i<S;i++){k[i]=kof(P,S,i,-1); F+=1LL<<k[i];}
  *Fout=F; long long best=1LL<<60;
  for(int y=0;y<S;y++){ long long D=0; for(int r=0;r<S;r++) if(r!=y){ int kk=kof(P,S,r,y); D+=(1LL<<kk)-(1LL<<k[r]);}
    long long mg=(1LL<<k[y])-D; if(mg<best)best=mg;}
  return (double)best;}
int main(int argc,char**argv){ PI=acos(-1.0); U=atof(argv[1]); S=atoi(argv[2]); long iters=atol(argv[3]); int R=atoi(argv[4]);
  rs=88172645463325252ULL^(unsigned long long)atol(argv[5])*2654435761ULL; for(int w=0;w<10;w++)rnd();
  LAM=2*PI/U; AMAX=PI-LAM; double bestm=-1e18; double bestP[MAXS][2]; long long bestF=0;
  for(int r=0;r<R;r++){ double P[MAXS][2],Q[MAXS][2];
    for(int i=0;i<S;i++){P[i][0]=gauss();P[i][1]=gauss();}
    long long F; double sc=margin(P,&F); double T=1.0, step=0.3;
    for(long it=0;it<iters;it++){ memcpy(Q,P,sizeof(double)*2*S);
      int mv=(int)(rnd()*2);
      if(mv==0){int j=(int)(rnd()*S); Q[j][0]+=step*gauss(); Q[j][1]+=step*gauss();}
      else { for(int i=0;i<S;i++){Q[i][0]+=0.1*step*gauss(); Q[i][1]+=0.1*step*gauss();}}
      long long F2; double sc2=margin(Q,&F2);
      if(sc2>=sc || rnd()<exp((sc2-sc)/T)){ memcpy(P,Q,sizeof(double)*2*S); sc=sc2; F=F2;
        if(sc>bestm){bestm=sc; bestF=F; memcpy(bestP,P,sizeof(double)*2*S);} }
      T*=0.99995; if(T<1e-3)T=1e-3; if(it%20000==19999){step*=0.8; if(step<1e-4)step=0.3;}
    }}
  printf("u=%.7f s=%d best_margin=%g F=%lld k=", U,S,bestm,bestF);
  for(int i=0;i<S;i++) printf("%d ", kof(bestP,S,i,-1)); printf("\n");
  if(bestm>0) for(int i=0;i<S;i++) printf("  %.10f %.10f\n",bestP[i][0],bestP[i][1]);
  return 0;}
