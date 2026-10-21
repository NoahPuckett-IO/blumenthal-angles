"""Numerical tests of the proof routes for (R) in docs/STEP5-NOTES.md, Attempt 4.

Same discretisation as relaxation.py (m cells per half-turn, lambda = L*pi/m).

Usage:
  routes.py fixedsign m L          # route (b): largest compatible family whose members all equal 1 on cell 0
  routes.py split     m L trials   # route (c): random maximal families; can each be split into two parts that
                                   # become valid at (m-L, L) after deleting some L cells (any cells, possibly
                                   # different for the two parts)?  Lists the families where this fails.
  routes.py inflate   m L trials   # route (a) inside one class: random maximal c-change families, inflatable
                                   # to lambda = pi/n with the cyclic order of all changes fixed?
  routes.py points    m L trials   # random maximal c-change families: do n evaluation cells separate all pairs,
                                   # and can they be chosen so that every word keeps exactly c changes?
  routes.py pstar     m L s1 s2 ...  # least circle length P (units of lambda) at which the combinatorial type of
                                   # the given family is realisable; the grid reduction says P = k/w with k <= J
  routes.py realise   m L m2 L2 s1 s2 ...  # realise the type of the given (m, L) family with integer positions on
                                   # (m2, L2) and check the result; possible iff m2/L2 >= P* (grid reduction)

Needs networkx, numpy, scipy.
"""
import itertools
import random
import sys
from fractions import Fraction

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from percc import band, compatible
from relaxation import changes, graph, inflatable, random_family, runs_ok
from relaxation_sat import functions


def nchanges(s):
    return len(changes(s))


def deflatable_parts(F, L):
    """Bitmasks of the parts of F that stay a valid family at (m-L, L) after deleting some L cells."""
    m, N = len(F[0]), len(F)
    good = set()
    for D in itertools.combinations(range(m), L):
        keep = [i for i in range(m) if i not in D]
        R = [[f[i] for i in keep] for f in F]
        ok = [i for i in range(N) if runs_ok(R[i], L)]
        adj = {i: {j for j in ok if j != i and R[i] != R[j] and compatible(R[i], R[j], L)} for i in ok}

        def bk(cur, P, X):
            if not P and not X:
                good.add(sum(1 << i for i in cur))
                return
            for v in list(P):
                bk(cur | {v}, P & adj[v], X & adj[v])
                P = P - {v}
                X = X | {v}
        bk(set(), set(ok), set())
    down = set()
    for g in good:
        sub = g
        while True:
            down.add(sub)
            if sub == 0:
                break
            sub = (sub - 1) & g
    return down


def word_changes(s, T):
    m = len(s)
    S = s + [1 - x for x in s]
    vals = [S[t] for t in T] + [S[T[0] + m]]
    return sum(vals[i] != vals[i + 1] for i in range(len(T)))


def separating_points(F, n, c):
    sep = False
    for T in itertools.combinations(range(len(F[0])), n):
        if len({tuple(f[t] for t in T) for f in F}) == len(F):
            sep = True
            if all(word_changes(f, T) == c for f in F):
                return True, True
    return sep, False


def type_milp(F, grid=None):
    """The constraint system of the grid-reduction lemma for the type of F: cyclic order of all changes
    (coincident changes share one variable), runs >= 1, and for each pair one chosen run of fg = -1 of
    length >= 1 (chosen by the solver). With grid=None, minimise the circle length P (units of lambda)
    and return P*. With grid=(m2, L2), look for integer positions on m2 cells with lambda = L2 cells and
    return the realised strings (or None)."""
    m = len(F[0])
    pts = sorted({p for s in F for p in changes(s)})
    idx = {p: k for k, p in enumerate(pts)}
    M = len(pts)
    cand = []
    for a, b in itertools.combinations(F, 2):
        q = sorted(set(changes(a)) ^ set(changes(b)))
        g = [(i, q[(k + 1) % len(q)]) for k, i in enumerate(q) if a[i] != b[i]]
        if g:  # empty means b = -a: coincident changes keep them opposite
            cand.append(g)
    nsel = sum(len(g) for g in cand)
    P = M  # index of the circle-length variable (unused when a grid is given)
    nv = M + 1 + nsel
    unit, length = (1, None) if grid is None else (grid[1], grid[0])
    BIG = 10.0 * (m if grid is None else grid[0])
    rows, lo = [], []

    def gap(i, j, need, sel=None):
        r = np.zeros(nv)
        r[idx[j]] += 1
        r[idx[i]] -= 1
        c = need
        if idx[j] <= idx[i]:  # the arc passes the cut once
            if length is None:
                r[P] += 1
            else:
                c -= length
        if sel is not None:
            r[M + 1 + sel] = -BIG
            c -= BIG
        rows.append(r)
        lo.append(c)

    for k in range(M):
        gap(pts[k], pts[(k + 1) % M], 0)
    for s in F:
        z = changes(s)
        for k in range(len(z)):
            gap(z[k], z[(k + 1) % len(z)], unit)
    sel = 0
    for g in cand:
        r = np.zeros(nv)
        for i, j in g:
            gap(i, j, unit, sel)
            r[M + 1 + sel] = 1
            sel += 1
        rows.append(r)
        lo.append(1)
    cost = np.zeros(nv)
    if grid is None:
        cost[P] = 1
        integ = [0] * (M + 1) + [1] * nsel
        ub = [10 * m] * (M + 1) + [1] * nsel
    else:
        integ = [1] * (M + 1) + [1] * nsel
        ub = [grid[0] - 1] * M + [0] + [1] * nsel
    res = milp(cost, constraints=LinearConstraint(np.array(rows), np.array(lo), np.inf),
               integrality=np.array(integ), bounds=Bounds([0] * nv, ub))
    if grid is None:
        return Fraction(res.x[P]).limit_denominator(1000)
    if res.status != 0:
        return None
    m2 = grid[0]
    pos = {p: int(round(res.x[idx[p]])) for p in pts}
    out = []
    for s in F:
        z = changes(s)
        start, cur = pos[z[0]], s[z[0]]  # the cell after the first change keeps its value
        marks = {(pos[p] - start) % m2 for p in z}
        seq = [0] * m2
        for d in range(2 * m2):  # walk a full turn, flipping at every change and at its antipode
            if d and d % m2 in marks:
                cur ^= 1
            cell = (start + d) % (2 * m2)
            if cell < m2:
                seq[cell] = cur
        out.append(seq)
    return out


def pstar(F):
    return type_milp(F)


if __name__ == "__main__":
    mode, m, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    n = band(m, L)
    if mode == "fixedsign":
        V = [v for v in functions(m, L) if v[0] == 1]
        _, w = nx.max_weight_clique(graph(V, L), weight=None)
        print(f"m={m} L={L} n={n}: largest family with value 1 on cell 0 = {w}; 2^(n-1) = {2 ** (n - 1)}")
    elif mode == "split":
        V = functions(m, L)
        rng = random.Random(3)
        stats = {}
        for _ in range(int(sys.argv[4])):
            F = random_family(V, L, rng)
            if len(F) <= 2 ** (n - 1):
                continue
            down = deflatable_parts(F, L)
            full = (1 << len(F)) - 1
            ok = any((full ^ a) in down for a in down)
            stats[(len(F), ok)] = stats.get((len(F), ok), 0) + 1
            if not ok:
                print("   no split:", " ".join("".join(map(str, s)) for s in F), flush=True)
        print(f"m={m} L={L} n={n}: (size, splits into two deflatable parts) -> {dict(sorted(stats.items()))}")
    elif mode in ("inflate", "points"):
        V = functions(m, L)
        rng = random.Random(7 if mode == "inflate" else 11)
        for c in range(1, n + 1, 2):
            Vc = [v for v in V if nchanges(v) == c]
            stats = {}
            for _ in range(int(sys.argv[4])):
                F = random_family(Vc, L, rng)
                if mode == "inflate":
                    key = (len(F), len(F) < 2 or inflatable(F, m, m / n))
                else:
                    key = (len(F),) + separating_points(F, n, c)
                stats[key] = stats.get(key, 0) + 1
                if not all(key[1:]):
                    print(f"   c={c} {key}:", " ".join("".join(map(str, s)) for s in F), flush=True)
            what = "(size, inflatable)" if mode == "inflate" else "(size, n cells separate, ... keeping c changes)"
            print(f"m={m} L={L} n={n} c={c}: {what} -> {dict(sorted(stats.items()))}", flush=True)
    elif mode == "pstar":
        F = [[int(ch) for ch in w] for w in sys.argv[4:]]
        J = sum(nchanges(f) for f in F)
        P = pstar(F)
        print(f"size={len(F)} J={J} grid m/L={m}/{L}={m / L:.4f} P*={P}={float(P):.4f}"
              f" ({'not ' if P > n else ''}inflatable to pi/{n})")
    elif mode == "realise":
        m2, L2 = int(sys.argv[4]), int(sys.argv[5])
        F = [[int(ch) for ch in w] for w in sys.argv[6:]]
        R = type_milp(F, (m2, L2))
        ok = R is not None and all(runs_ok(r, L2) for r in R) and len({tuple(r) for r in R}) == len(R) and \
            all(compatible(a, b, L2) for a, b in itertools.combinations(R, 2)) and \
            [nchanges(r) for r in R] == [nchanges(f) for f in F]
        print(f"size={len(F)} P*={pstar(F)}: type realised on ({m2},{L2}) [ratio {m2 / L2:.4f}]: {ok}")
        if ok:
            print("  ", " ".join("".join(map(str, r)) for r in R))
