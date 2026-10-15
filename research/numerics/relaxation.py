"""Experiments on the one-dimensional relaxation (R) of the first band (see docs/STEP5-NOTES.md, Attempt 3).

Discretisation. T = R/piZ is cut into m cells. A sign function is a 0/1 string s of length m, extended to
S^1 by s[i+m] = 1 - s[i] (oddness). Runs of the extended string must have length >= L cells, and two
functions are compatible when the cyclic XOR of their strings contains a run of >= L ones. This is (R)
with lambda = L*pi/m; the first band for n is 2/(2n+1) < L/m <= 1/n.

Usage:
  relaxation.py clique  m L          # largest compatible family (exact)
  relaxation.py chif    m L          # fractional chromatic number of the compatibility graph
  relaxation.py tests   m L n trials # random maximal families: fixed test points vs. inflation to pi/n
  relaxation.py family  m L n s1 s2 ... # the same two checks for an explicit family

Needs networkx, numpy, scipy.
"""
import itertools
import random
import sys

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp


def functions(m, L):
    out = []
    for s in itertools.product([0, 1], repeat=m):
        S = list(s) + [1 - x for x in s]
        ch = [i for i in range(2 * m) if S[i] != S[i - 1]]
        if all(b - a >= L for a, b in zip(ch, ch[1:] + [ch[0] + 2 * m])):
            out.append(list(s))
    return out


def compatible(a, b, L):
    d = [x ^ y for x, y in zip(a, b)]
    if all(d):
        return True
    best = cur = 0
    for x in d + d:
        cur = cur + 1 if x else 0
        best = max(best, cur)
    return best >= L


def graph(V, L):
    G = nx.Graph()
    G.add_nodes_from(range(len(V)))
    G.add_edges_from((i, j) for i in range(len(V)) for j in range(i + 1, len(V)) if compatible(V[i], V[j], L))
    return G


def random_family(V, L, rng):
    order = V[:]
    rng.shuffle(order)
    F = []
    for s in order:
        if all(compatible(s, f, L) for f in F):
            F.append(s)
    return F


def test_number(F, m):
    """Least number of evaluation cells separating every pair of F."""
    sets = [{i for i in range(m) if a[i] != b[i]} for a, b in itertools.combinations(F, 2)]
    for k in range(1, m + 1):
        for T in itertools.combinations(range(m), k):
            if all(any(t in s for t in T) for s in sets):
                return k


def changes(s):
    m = len(s)
    z = [i for i in range(1, m) if s[i] != s[i - 1]]
    return ([0] if s[m - 1] == s[0] else []) + z


def inflatable(F, m, lam):
    """Can the sign changes be moved, keeping their cyclic order, so that every run and some
    disagreement run of every pair has length >= lam (in cells)?"""
    pts = sorted({p for s in F for p in changes(s)})
    idx = {p: k for k, p in enumerate(pts)}
    M = len(pts)
    cand = []
    for a, b in itertools.combinations(F, 2):
        q = sorted(set(changes(a)) ^ set(changes(b)))
        g = [(i, q[(k + 1) % len(q)]) for k, i in enumerate(q) if a[i] != b[i]]
        if g:  # empty means b = -a, which disagree everywhere
            cand.append(g)
    nsel = sum(len(g) for g in cand)
    BIG = 2 * m
    rows, lo = [], []

    def gap(i, j, need, sel=None):
        r = np.zeros(M + nsel)
        r[idx[j]] += 1
        r[idx[i]] -= 1
        c = need - (m if idx[j] <= idx[i] else 0)
        if sel is not None:
            r[M + sel] = -BIG
            c -= BIG
        rows.append(r)
        lo.append(c)

    for k in range(M):
        gap(pts[k], pts[(k + 1) % M], 0)
    for s in F:
        z = changes(s)
        for k in range(len(z)):
            gap(z[k], z[(k + 1) % len(z)], lam)
    sel = 0
    for g in cand:
        r = np.zeros(M + nsel)
        for i, j in g:
            gap(i, j, lam, sel)
            r[M + sel] = 1
            sel += 1
        rows.append(r)
        lo.append(1)
    res = milp(np.zeros(M + nsel), constraints=LinearConstraint(np.array(rows), np.array(lo), np.inf),
               integrality=np.array([0] * M + [1] * nsel), bounds=Bounds([0] * (M + nsel), [m] * M + [1] * nsel))
    return res.status == 0


if __name__ == "__main__":
    mode, m, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    V = functions(m, L)
    if mode == "clique":
        _, w = nx.max_weight_clique(graph(V, L), weight=None)
        print(f"m={m} L={L} L/m={L / m:.4f} functions={len(V)} largest family={w}")
    elif mode == "chif":
        G = graph(V, L)
        I = list(nx.find_cliques(nx.complement(G)))
        A = np.zeros((len(V), len(I)))
        for k, S in enumerate(I):
            A[list(S), k] = 1
        res = linprog(np.ones(len(I)), A_ub=-A, b_ub=-np.ones(len(V)), bounds=(0, None), method="highs")
        print(f"m={m} L={L} omega={nx.max_weight_clique(G, weight=None)[1]} chi_f={res.fun:.4f}")
    elif mode == "tests":
        n, trials = int(sys.argv[4]), int(sys.argv[5])
        rng = random.Random(1)
        stats = {}
        for _ in range(trials):
            F = random_family(V, L, rng)
            key = (len(F), test_number(F, m) <= n, inflatable(F, m, m / n))
            stats[key] = stats.get(key, 0) + 1
            if not (key[1] and key[2]):
                print("  ", key, " ".join("".join(map(str, s)) for s in F), flush=True)
        print(f"m={m} L={L} n={n}: (size, n points suffice, inflates to pi/n) -> count")
        for k, v in sorted(stats.items()):
            print("  ", k, v)
    elif mode == "family":
        n = int(sys.argv[4])
        F = [[int(c) for c in w] for w in sys.argv[5:]]
        assert all(len(f) == m and f in V for f in F), "not a valid function"
        assert all(compatible(a, b, L) for a, b in itertools.combinations(F, 2)), "not compatible"
        print(f"size={len(F)} evaluation points needed={test_number(F, m)} inflates to pi/n: {inflatable(F, m, m / n)}")
