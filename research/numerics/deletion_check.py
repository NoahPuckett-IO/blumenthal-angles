"""Check whether a configuration is 'irreducible' for deletion induction:
for every y, Delta(y) = F(Q - y) - (F(Q) - 2^k(y)) < 2^k(y), i.e. deleting any single point
strictly lowers the Sendov weight F. usage: deletion_check.py u cfg.txt"""
import sys
from mpmath import mpf, pi
from weights import read_cfg, max_angle, k_of, weight

u = mpf(sys.argv[1]); Q = read_cfg(sys.argv[2])
print("max angle/pi =", float(max_angle(Q) / pi), " allowed <=", float(1 - 2 / u))
ks = [k_of(Q, i, u) for i in range(len(Q))]
F = weight(Q, u)
print("k =", ks, " F =", F)
for y in range(len(Q)):
    delta = sum(2 ** k_of(Q, r, u, skip=y) - 2 ** ks[r] for r in range(len(Q)) if r != y)
    print(f"  delete point {y}: gain elsewhere {delta}, its weight {2 ** ks[y]}"
          f" -> {'reducible' if delta >= 2 ** ks[y] else 'NOT reducible'}")
