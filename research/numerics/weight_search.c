// Annealing search for violations of the Key Claim behind Sendov's Lemma 4.1.
// usage: kc u s iters restarts seed
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXS 32
static double PI;
static int S;
static double U, LAM, AMAX;

static unsigned long long rs;
static double rnd(void) {  // xorshift
  rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
  return (rs >> 11) * (1.0 / 9007199254740992.0);
}
static double gauss(void) {
  double a = rnd(), b = rnd();
  if (a < 1e-300) a = 1e-300;
  return sqrt(-2 * log(a)) * cos(2 * PI * b);
}
static int cmpd(const void *a, const void *b) {
  double x = *(const double *)a, y = *(const double *)b;
  return (x > y) - (x < y);
}

// max angle over all triples
static double maxangle(double (*P)[2]) {
  double best = 0;
  for (int i = 0; i < S; i++) {
    double a[MAXS]; int m = 0;
    for (int j = 0; j < S; j++) if (j != i)
      a[m++] = atan2(P[j][1] - P[i][1], P[j][0] - P[i][0]);
    for (int x = 0; x < m; x++) for (int y = x + 1; y < m; y++) {
      double d = fabs(a[x] - a[y]);
      if (d > PI) d = 2 * PI - d;
      if (d > best) best = d;
    }
  }
  return best;
}

static void kvals(double (*P)[2], int *k, double *soft) {
  for (int i = 0; i < S; i++) {
    double t[MAXS]; int m = 0;
    for (int j = 0; j < S; j++) if (j != i) {
      double a = atan2(P[j][1] - P[i][1], P[j][0] - P[i][0]);
      a = fmod(a + 2 * PI, PI);
      t[m++] = a;
    }
    qsort(t, m, sizeof(double), cmpd);
    int kk = 0; double sf = 0;
    for (int g = 0; g < m; g++) {
      double gap = (g + 1 < m ? t[g + 1] : t[0] + PI) - t[g];
      double x = gap / LAM;
      int c = (int)floor(x + 1e-12) - 1;
      if (c > 0) kk += c;
      if (x > 1) sf += x - 1;
    }
    k[i] = kk; soft[i] = sf;
  }
}

static double score(double (*P)[2], long long *Fout) {
  int k[MAXS]; double sf[MAXS];
  double ma = maxangle(P);
  if (ma > AMAX) { *Fout = -1; return -1000.0 * (ma - AMAX); }
  kvals(P, k, sf);
  long long F = 0; double s2 = 0;
  for (int i = 0; i < S; i++) { F += 1LL << k[i]; s2 += pow(2.0, sf[i]); }
  *Fout = F;
  return F + 1e-3 * s2;  // tiny tie-break toward larger gaps
}

static long long boundf(double u) {
  int n = (int)floor(u / 2);
  if (u < 2 * n + 1) return 1LL << n;
  return (1LL << n) + (n >= 2 ? (1LL << (n - 2)) : 0);
}

int main(int argc, char **argv) {
  PI = acos(-1.0);
  U = atof(argv[1]); S = atoi(argv[2]);
  long iters = atol(argv[3]); int restarts = atoi(argv[4]);
  rs = 88172645463325252ULL ^ (unsigned long long)atol(argv[5]) * 2654435761ULL;
  for (int w = 0; w < 10; w++) rnd();
  LAM = 2 * PI / U; AMAX = PI - LAM;
  long long B = boundf(U), bestF = 0;
  double bestP[MAXS][2];
  for (int r = 0; r < restarts; r++) {
    double P[MAXS][2], Q[MAXS][2];
    for (int i = 0; i < S; i++) { P[i][0] = gauss(); P[i][1] = gauss(); }
    long long F; double sc = score(P, &F);
    double T = 0.5, step = 0.3;
    for (long it = 0; it < iters; it++) {
      memcpy(Q, P, sizeof(double) * 2 * S);
      int mv = (int)(rnd() * 3);
      if (mv == 0) { int j = (int)(rnd() * S); Q[j][0] += step * gauss(); Q[j][1] += step * gauss(); }
      else if (mv == 1) { int j = (int)(rnd() * S); double f = exp(0.3 * gauss());
        // scale a point toward/away from centroid
        double cx = 0, cy = 0; for (int i = 0; i < S; i++) { cx += P[i][0]; cy += P[i][1]; }
        cx /= S; cy /= S; Q[j][0] = cx + f * (Q[j][0] - cx); Q[j][1] = cy + f * (Q[j][1] - cy); }
      else { for (int i = 0; i < S; i++) { Q[i][0] += 0.1 * step * gauss(); Q[i][1] += 0.1 * step * gauss(); } }
      long long F2; double sc2 = score(Q, &F2);
      if (sc2 >= sc || rnd() < exp((sc2 - sc) / T)) {
        memcpy(P, Q, sizeof(double) * 2 * S); sc = sc2; F = F2;
        if (F > bestF) { bestF = F; memcpy(bestP, P, sizeof(double) * 2 * S); }
      }
      T *= 0.99995; if (T < 1e-3) T = 1e-3;
      if (it % 20000 == 19999) { step *= 0.8; if (step < 1e-4) step = 0.3; }
    }
  }
  int k[MAXS]; double sf[MAXS];
  kvals(bestP, k, sf);
  printf("u=%.9f s=%d bestF=%lld bound=%lld%s  k=", U, S, bestF, B, bestF > B ? " VIOLATION" : "");
  for (int i = 0; i < S; i++) printf("%d ", k[i]);
  printf(" maxang/pi=%.6f\n", maxangle(bestP) / PI);
  if (bestF > B || getenv("SHOW")) for (int i = 0; i < S; i++) printf("  %.12f %.12f\n", bestP[i][0], bestP[i][1]);
  return 0;
}
