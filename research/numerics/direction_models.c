// Pseudo-configurations: directions d[a][b] in S^1 for all pairs, d[b][a]=d[a][b]+pi,
// every triple consistent (u_ab,u_bc,u_ca positively span R^2), every angle <= pi-lam.
// Maximize F = sum 2^kappa(q). usage: pseudo u s iters restarts seed
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXS 16
static double PI,U,LAM,AMAX; static int S;
static unsigned long long rs;
static double rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (rs>>11)*(1.0/9007199254740992.0);}
static double gauss(void){ double a=rnd(),b=rnd(); if(a<1e-300)a=1e-300; return sqrt(-2*log(a))*cos(2*PI*b);}
static int cmpd(const void*a,const void*b){double x=*(const double*)a,y=*(const double*)b;return (x>y)-(x<y);}
static double D[MAXS][MAXS]; static int NOTRI=0;
static double ang(double a,double b){ double d=fmod(fabs(a-b),2*PI); if(d>PI)d=2*PI-d; return d;}
static double dir(int a,int b){ return a<b? D[a][b] : fmod(D[b][a]+PI,2*PI);}
// violation measure: angles over AMAX, triangles not positively spanning
static double viol(void){ double v=0;
  for(int q=0;q<S;q++) for(int a=0;a<S;a++) if(a!=q) for(int b=a+1;b<S;b++) if(b!=q){
    double t=ang(dir(q,a),dir(q,b)); if(t>AMAX) v+=t-AMAX; }
  for(int a=0;a<S;a++) for(int b=a+1;b<S;b++) for(int c=b+1;c<S;c++){
    // angles of the would-be triangle: at a between b,c; at b between a,c; at c between a,b. Consistent iff sum == pi
    double s3=ang(dir(a,b),dir(a,c))+ang(dir(b,a),dir(b,c))+ang(dir(c,a),dir(c,b));
    if(!NOTRI) v+=fabs(s3-PI); }
  return v;}
static int kof(int q){ double t[MAXS]; int m=0; for(int r=0;r<S;r++) if(r!=q) t[m++]=fmod(dir(q,r),PI);
  qsort(t,m,sizeof(double),cmpd); int k=0;
  for(int g=0;g<m;g++){ double gap=(g+1<m?t[g+1]:t[0]+PI)-t[g]; int c=(int)floor(gap/LAM+1e-12)-1; if(c>0)k+=c;} return k;}
static long long Fv(void){ long long F=0; for(int q=0;q<S;q++) F+=1LL<<kof(q); return F;}
static long long bound(double u){ int n=(int)floor(u/2); return (u<2*n+1)?(1LL<<n):((1LL<<n)+(1LL<<(n-2)));}
int main(int argc,char**argv){ PI=acos(-1.0); U=atof(argv[1]); S=atoi(argv[2]); long iters=atol(argv[3]); int R=atoi(argv[4]);
  rs=88172645463325252ULL^(unsigned long long)atol(argv[5])*2654435761ULL; for(int w=0;w<10;w++)rnd();
  LAM=2*PI/U; AMAX=PI-LAM; if(getenv("NOTRI")) NOTRI=1; long long best=0; double BD[MAXS][MAXS];
  for(int r=0;r<R;r++){ double P[MAXS][2];
    // start from a real configuration
    for(int i=0;i<S;i++){P[i][0]=gauss();P[i][1]=gauss();}
    for(int a=0;a<S;a++) for(int b=a+1;b<S;b++) D[a][b]=fmod(atan2(P[b][1]-P[a][1],P[b][0]-P[a][0])+2*PI,2*PI);
    double v=viol(); long long F=Fv(); double sc = v>1e-9? -1000*v : (double)F;
    double T=1.0, step=0.3;
    for(long it=0;it<iters;it++){ int a=(int)(rnd()*S), b=(int)(rnd()*S); if(a==b) continue; if(a>b){int t=a;a=b;b=t;}
      double old=D[a][b]; D[a][b]=fmod(old+step*gauss()+4*PI,2*PI);
      double v2=viol(); long long F2=Fv(); double sc2 = v2>1e-9? -1000*v2 : (double)F2;
      if(sc2>=sc || rnd()<exp((sc2-sc)/T)){ sc=sc2; if(v2<=1e-9 && F2>best){best=F2; memcpy(BD,D,sizeof(D));}}
      else D[a][b]=old;
      T*=0.99995; if(T<1e-3)T=1e-3; if(it%20000==19999){step*=0.8; if(step<1e-4)step=0.3;}
    }}
  printf("u=%.6f s=%d pseudo best F=%lld bound=%lld %s\n",U,S,best,bound(U),best>bound(U)?"EXCEEDS":"");
  if(best>bound(U) || getenv("SHOW")){ memcpy(D,BD,sizeof(D)); printf("MATRIX ["); for(int a=0;a<S;a++){ printf("%s[",a?",":""); for(int b=0;b<S;b++) printf("%s%.15f",b?",":"", a==b?-1.0:dir(a,b)); printf("]");} printf("]\n"); }
  return 0;}
