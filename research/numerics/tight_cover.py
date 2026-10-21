"""Tight-cycle cover search for one change-count class (docs/STEP5-NOTES.md, Attempt 4.7).

Sharpened grid reduction: if the combinatorial type of a family has critical circle length P* = k/w
(lowest terms), the type is realisable on the grid (k, w) with a sign change at EVERY one of the k cell
boundaries (the critical cycle is tight, advances one lambda = w cells per lambda-edge, and gcd(k, w) = 1).
So "no K compatible c-change functions in band n" follows from
  - a grid (m0, L0) on which the class maximum is < K (this covers every P* <= m0/L0), and
  - for every k/w in lowest terms with m0/L0 < k/w <= P_J (J = K*c, k <= J): no K compatible c-change
    functions on (k, w) whose change positions cover all k boundaries.

Usage:
  tight_cover.py plan  n c K m0 L0          # list the grids (k, w) still to search after (m0, L0)
  tight_cover.py run   k w c K [W] [T]      # covered search on one grid: CP-SAT, W workers, T seconds

Needs numpy, ortools.
"""
import itertools
import math
import sys
import time
from fractions import Fraction

import numpy as np

from percc import functions


def plan(n, c, K, m0, L0):
    J = K * c
    lo = Fraction(m0, L0)
    out = set()
    for w in range(1, 2 * J + 2):
        for k in range(1, J + 1):
            f = Fraction(k, w)
            if lo < f and 2 * f.numerator < (2 * n + 1) * f.denominator:
                out.add(f)
    return sorted(out)


def changes_mask(s):
    m = len(s)
    S = list(s) + [1 - x for x in s]
    return sum(1 << i for i in range(m) if S[i] != S[i - 1])


def compat_matrix(V, L):
    """Boolean compatibility matrix via 64-bit masks of the XOR (m <= 63)."""
    m = len(V[0])
    full = (1 << m) - 1
    A = np.array([sum(b << i for i, b in enumerate(v)) for v in V], dtype=np.uint64)
    N = len(V)
    C = np.zeros((N, N), dtype=bool)
    mm = np.uint64(m)
    mask = np.uint64(full)
    for i in range(N):
        d = A ^ A[i]
        run = d.copy()  # run[x] has bit t set iff d has ones at t, t+1, ..., t+j (cyclic)
        for j in range(1, L):
            rot = ((d >> np.uint64(j)) | (d << (mm - np.uint64(j)))) & mask
            run &= rot
        C[i] = (run != 0) | (d == mask)
    np.fill_diagonal(C, False)
    return C


def run(k, w, c, K, workers=8, T=None, arcs=False):
    from ortools.sat.python import cp_model
    V = functions(k, w, c)
    N = len(V)
    t0 = time.time()
    C = compat_matrix(V, w)
    masks = [changes_mask(v) for v in V]
    md = cp_model.CpModel()
    x = [md.new_bool_var(f"x{i}") for i in range(N)]
    # incompatibility: greedy clique cover of the complement graph, one AtMostOne per clique
    inc = ~C
    np.fill_diagonal(inc, False)
    left = inc.copy()  # incompatible pairs not yet covered by a clique
    ncl = 0
    for i in np.argsort(-inc.sum(1)):
        while left[i].any():
            clique = [i]
            pool = np.flatnonzero(inc[i])
            # grow greedily, preferring members that still have uncovered pairs with i
            pool = pool[np.argsort(~left[i, pool], kind="stable")]
            while len(pool):
                j = pool[0]
                clique.append(j)
                pool = pool[1:][inc[j, pool[1:]]]
            md.add_at_most_one(x[a] for a in clique)
            cl = np.array(clique)
            left[np.ix_(cl, cl)] = False
            ncl += 1
    for p in range(k):
        md.add_bool_or([x[i] for i in range(N) if masks[i] >> p & 1])
    if arcs:
        # every boundary p starts a tight lambda-arc [p, p+w] of the critical cycle: either a run of one
        # member (changes at p and p+w) or a whole run of fg = -1 of exactly w cells for a pair
        A = np.array([sum(b << q for q, b in enumerate(v)) for v in V], dtype=np.uint64)
        full = np.uint64((1 << k) - 1)
        bit = [np.uint64(1 << q) for q in range(k)]
        y = {}
        for p in range(k):
            ones = np.uint64(sum(1 << ((p + q) % k) for q in range(w)))
            zero = bit[(p - 1) % k] | bit[(p + w) % k]
            lits = [x[i] for i in range(N) if masks[i] >> p & 1 and masks[i] >> ((p + w) % k) & 1]
            for i in (i for i in range(N) if masks[i] >> p & 1):
                d = A ^ A[i]
                hit = np.flatnonzero(((d & ones) == ones) & ((d & zero) == 0))
                for j in hit:
                    key = (min(i, j), max(i, j))
                    if key not in y:
                        y[key] = md.new_bool_var("")
                        md.add_implication(y[key], x[key[0]])
                        md.add_implication(y[key], x[key[1]])
                    lits.append(y[key])
            md.add_bool_or(lits)
        ncl = (ncl, len(y))
    md.add(sum(x) >= K)
    s = cp_model.CpSolver()
    s.parameters.num_workers = workers
    s.parameters.symmetry_level = 4
    if T:
        s.parameters.max_time_in_seconds = T
    st = s.solve(md)
    name = s.status_name(st)
    fam = [V[i] for i in range(N) if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) and s.value(x[i])]
    return name, N, ncl, time.time() - t0, fam


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "plan":
        n, c, K, m0, L0 = map(int, sys.argv[2:7])
        fr = plan(n, c, K, m0, L0)
        print(f"n={n} c={c} K={K} J={K * c}: after ({m0},{L0}) search these grids with full cover:")
        for f in fr:
            print(f"  ({f.numerator},{f.denominator})  ratio {float(f):.4f}  "
                  f"{len(functions(f.numerator, f.denominator, c))} functions")
    elif mode == "run":
        k, w, c, K = map(int, sys.argv[2:6])
        W = int(sys.argv[6]) if len(sys.argv) > 6 else 8
        T = float(sys.argv[7]) if len(sys.argv) > 7 and sys.argv[7] != "--arcs" else None
        name, N, ncl, dt, fam = run(k, w, c, K, W, T, "--arcs" in sys.argv)
        verdict = {"INFEASIBLE": f"no covering family of {K}", "OPTIMAL": "FOUND", "FEASIBLE": "FOUND"}.get(name, name)
        print(f"grid ({k},{w}) c={c} K={K}: {N} functions, {ncl} cliques -> {name}: {verdict} ({dt:.0f}s)")
        if fam:
            print("family:", " ".join("".join(map(str, v)) for v in fam))
