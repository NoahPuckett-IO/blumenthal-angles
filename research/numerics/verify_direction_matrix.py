"""Verify a direction matrix (JSON list of lists, M[a][b] = direction of the vector a->b in radians, diagonal ignored):
antisymmetry, per-point angle bound <= (1-2/u)pi, optional triangle consistency, kappa values and F.
usage: verify_direction_matrix.py u file"""
import sys, json, math
from mpmath import mp, mpf, pi, floor
mp.dps = 30
u = mpf(sys.argv[1]); txt = open(sys.argv[2]).read(); M = json.loads(txt[txt.index('['):])
s = len(M); lam = 2*pi/u
def ang(a, b):
    d = abs(mpf(a) - mpf(b)) % (2*pi); return min(d, 2*pi - d)
anti = max(ang(M[a][b], M[b][a] + math.pi) for a in range(s) for b in range(s) if a != b)
worst = max(ang(M[q][a], M[q][b]) for q in range(s) for a in range(s) for b in range(s) if len({q, a, b}) == 3)
tri = max(abs(ang(M[a][b], M[a][c]) + ang(M[b][a], M[b][c]) + ang(M[c][a], M[c][b]) - pi)
          for a in range(s) for b in range(s) for c in range(s) if a < b < c)
print("antisymmetry error", float(anti), "| max angle/pi", float(worst/pi), "<= bound", float(1 - 2/u), worst <= pi - lam)
print("max triangle angle-sum defect (0 = every triple consistent):", float(tri))
F = 0
for q in range(s):
    ds = sorted(mpf(M[q][r]) % pi for r in range(s) if r != q)
    gaps = [ds[t+1] - ds[t] for t in range(len(ds)-1)] + [ds[0] + pi - ds[-1]]
    k = sum(max(int(floor(g/lam)) - 1, 0) for g in gaps); F += 2**k
    print(f"  point {q}: kappa = {k}, gaps/lam = {[round(float(g/lam), 3) for g in gaps]}")
print("F =", F)
