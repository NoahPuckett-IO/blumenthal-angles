"""Shared helpers: max angle, Sendov weights k_u(q), and deletion gains, in high precision."""
from mpmath import mp, mpf, atan2, pi, floor
mp.dps = 50


def read_cfg(path):
    return [tuple(mpf(x) for x in line.split()) for line in open(path) if line.strip()]


def max_angle(Q):
    best = mpf(0)
    for i, q in enumerate(Q):
        vs = [atan2(p[1] - q[1], p[0] - q[0]) for j, p in enumerate(Q) if j != i]
        for a in range(len(vs)):
            for b in range(a + 1, len(vs)):
                t = abs(vs[a] - vs[b])
                if t > pi:
                    t = 2 * pi - t
                best = max(best, t)
    return best


def gaps(Q, i, skip=None):
    ds = sorted(atan2(p[1] - Q[i][1], p[0] - Q[i][0]) % pi
                for j, p in enumerate(Q) if j != i and j != skip)
    return [ds[t + 1] - ds[t] for t in range(len(ds) - 1)] + [ds[0] + pi - ds[-1]]


def k_of(Q, i, u, skip=None):
    lam = 2 * pi / u
    return sum(max(int(floor(g / lam)) - 1, 0) for g in gaps(Q, i, skip))


def weight(Q, u):
    return sum(2 ** k_of(Q, i, u) for i in range(len(Q)))
