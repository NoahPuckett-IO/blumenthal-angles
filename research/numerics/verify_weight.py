"""Verify a configuration: max angle vs (1-2/u)pi, the weights k_u(q), F_u(Q), and how far each
gap/lambda is from an integer (robustness of the floors). usage: verify_weight.py u cfg.txt"""
import sys
from mpmath import mpf, pi, floor
from weights import read_cfg, max_angle, gaps, k_of, weight

u = mpf(sys.argv[1]); Q = read_cfg(sys.argv[2]); lam = 2 * pi / u
ma = max_angle(Q)
print(f"s = {len(Q)}, u = {u}: max angle/pi = {float(ma / pi):.9f} <= {float(1 - 2 / u):.9f}: {ma <= pi - lam}")
for i in range(len(Q)):
    g = [x / lam for x in gaps(Q, i)]
    rob = min(abs(x - floor(x + mpf(1) / 2)) for x in g)
    print(f"  point {i}: k = {k_of(Q, i, u)}, gaps/lambda = {[round(float(x), 4) for x in g]}, "
          f"min distance to an integer = {float(rob):.2e}")
print("F_u(Q) =", weight(Q, u))
