// For configurations Q found by annealing (maximize F), search arc partitions of RP^1
// into n+1 half-open arcs of width <= lam, minimizing F_bad = sum over bad q of 2^k(q),
// bad <=> touched(q) + k(q) > n.  Conjecture A (u<2n+1): min F_bad = 0.
// Conjecture B (u<2n+2): min F_bad <= 2^(n-1).
// usage: part u s iters restarts seed  [mode: 0 = maximize F then test; 1 = adversarial]
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXS 24
static double PI,U,LAM,AMAX; static int S,NN;
static unsigned long long rs;
static double rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (rs>>11)*(1.0/9007199254740992.0);}
static double gauss(void){ double a=rnd(),b=rnd(); if(a<1e-300)a=1e-300; return sqrt(-2*log(a))*cos(2*PI*b);}
static int cmpd(const void*a,const void*b){double x=*(const double*)a,y=*(const double*)b;return (x>y)-(x<y);}
static double maxangle(double (*P)[2]){ double best=0;
  for(int i=0;i<S;i++){ double a[MAXS]; int m=0;
    for(int j=0;j<S;j++) if(j!=i) a[m++]=atan2(P[j][1]-P[i][1],P[j][0]-P[i][0]);
    for(int x=0;x<m;x++) for(int y=x+1;y<m;y++){ double d=fabs(a[x]-a[y]); if(d>PI)d=2*PI-d; if(d>best)best=d;}}
  return best;}
static double DIR[MAXS][MAXS]; static int ND[MAXS]; static int K[MAXS];
static void dirs(double (*P)[2]){
  for(int i=0;i<S;i++){ int m=0; for(int j=0;j<S;j++) if(j!=i){ double a=atan2(P[j][1]-P[i][1],P[j][0]-P[i][0]); DIR[i][m++]=fmod(a+2*PI,PI);}
    qsort(DIR[i],m,sizeof(double),cmpd); ND[i]=m; int kk=0;
    for(int g=0;g<m;g++){ double gap=(g+1<m?DIR[i][g+1]:DIR[i][0]+PI)-DIR[i][g]; int c=(int)floor(gap/LAM+1e-12)-1; if(c>0)kk+=c;}
    K[i]=kk;}}
static long long Fval(void){ long long F=0; for(int i=0;i<S;i++) F+=1LL<<K[i]; return F;}
// partition: cuts c[0..NN] sorted in [c0, c0+pi); arcs [c_i, c_{i+1})
static double RATIO;
static long long fbad(const double *cut){
  long long fb=0; double kr=0; long long F=0;
  for(int q=0;q<S;q++){ int touched=0; int hit[64]={0};
    for(int t=0;t<ND[q];t++){ double d=DIR[q][t]; // locate arc
      double x=fmod(d-cut[0]+2*PI,PI); int a=0; while(a<NN && x>=cut[a+1]-cut[0]) a++; if(!hit[a]){hit[a]=1;touched++;}}
    kr += (double)(1LL<<(NN-touched)); F += 1LL<<K[q]; }
  // deficit scaled x5 to keep integers: 5*(RATIO*F - sum 2^nu)
  double d = RATIO*F - kr; return (long long)llround(5*d);}
static void randcut(double *cut){ // n+1 arcs widths lam-d_i, sum d_i = (n+1)lam - pi
  double tot=NN*LAM-PI, e[64], se=0; for(int i=0;i<NN;i++){ e[i]=-log(rnd()+1e-300); if(rnd()<0.5) e[i]*=0.01; se+=e[i];}
  cut[0]=rnd()*PI; for(int i=0;i<NN;i++) cut[i+1]=cut[i]+LAM-tot*e[i]/se; }
static long long bestpart(int tries, double *bc){
  long long best=1LL<<60; (void)0; double c[64];
  for(int t=0;t<tries;t++){ randcut(c); long long f=fbad(c);
    // local improvement: jiggle
    for(int it=0;it<200 && f>-1000000;it++){ double c2[64]; memcpy(c2,c,sizeof(double)*(NN+1));
      int i=(int)(rnd()*NN); double dd=(rnd()-0.5)*LAM*0.2; 
      if(i==0){ for(int j=0;j<=NN;j++) c2[j]+=dd; }
      else { c2[i]+=dd; if(c2[i]-c2[i-1]>LAM||c2[i+1]-c2[i]>LAM||c2[i]<=c2[i-1]||c2[i]>=c2[i+1]) continue; }
      long long f2=fbad(c2); if(f2<=f){f=f2; memcpy(c,c2,sizeof(double)*(NN+1));}}
    if(f<best){best=f; memcpy(bc,c,sizeof(double)*(NN+1));} if(best<=-1000000) break;}
  return best;}
int main(int argc,char**argv){ PI=acos(-1.0); U=atof(argv[1]); S=atoi(argv[2]); long iters=atol(argv[3]); int R=atoi(argv[4]);
  rs=88172645463325252ULL^(unsigned long long)atol(argv[5])*2654435761ULL; for(int w=0;w<10;w++)rnd();
  int mode=argc>6?atoi(argv[6]):0;
  LAM=2*PI/U; AMAX=PI-LAM; int n=(int)floor(U/2); NN=n+1;
  RATIO = (U<2*n+1)?2.0:1.6; long long thr=0;
  double worst=-1e18; long long wF=0, wFb=0; double WP[MAXS][2];
  for(int r=0;r<R;r++){ double P[MAXS][2],Q[MAXS][2];
    for(int i=0;i<S;i++){P[i][0]=gauss();P[i][1]=gauss();}
    double sc=-1e9; double T=1.0, step=0.3; double bc[64];
    for(long it=0;it<iters;it++){ memcpy(Q,P,sizeof(double)*2*S);
      if(rnd()<0.5){int j=(int)(rnd()*S); Q[j][0]+=step*gauss(); Q[j][1]+=step*gauss();}
      else for(int i=0;i<S;i++){Q[i][0]+=0.1*step*gauss(); Q[i][1]+=0.1*step*gauss();}
      double ma=maxangle(Q), sc2;
      if(ma>AMAX) sc2=-1000*(ma-AMAX)-1e6;
      else { dirs(Q); long long F=Fval();
        if(mode==0) sc2=(double)F;
        else { long long fb=bestpart(30,bc); sc2=(double)(fb-thr)+0.001*F; }}
      if(sc2>=sc || rnd()<exp((sc2-sc)/T)){ memcpy(P,Q,sizeof(double)*2*S); sc=sc2; }
      T*=0.9995; if(T<1e-3)T=1e-3; if(it%2000==1999){step*=0.8; if(step<1e-4)step=0.3;}
    }
    if(maxangle(P)<=AMAX){ dirs(P); long long F=Fval(); long long fb=bestpart(3000,bc);
      if((double)(fb-thr)>worst){worst=(double)(fb-thr); wF=F; wFb=fb; memcpy(WP,P,sizeof(double)*2*S);}
      printf("  restart %d: F=%lld minFbad=%lld thr=%lld %s k=",r,F,fb,thr,fb>thr?"FAIL":"ok");
      for(int i=0;i<S;i++) printf("%d ",K[i]); printf("\n"); }
  }
  printf("u=%.7f s=%d mode=%d worst(minFbad-thr)=%g (F=%lld Fbad=%lld)\n",U,S,mode,worst,wF,wFb);
  for(int i=0;i<S;i++) printf("  %.12f %.12f\n",WP[i][0],WP[i][1]);
  return 0;}
