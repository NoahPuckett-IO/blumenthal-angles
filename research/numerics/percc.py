"""Per-change-count classes of (R) and the finite-grid reduction (docs/STEP5-NOTES.md, Attempt 4).

Same discretisation as relaxation.py: T = R/piZ cut into m cells, lambda = L*pi/m, a sign function is a
0/1 string with runs >= L under the twisted wrap s[i+m] = 1 - s[i]. The class of c-change functions is
the set of strings with exactly c sign changes per half-turn (c odd).

Finite-grid reduction (proved in the notes): a family in band n with J sign changes in total is
realisable on every grid (m, L) with P_J <= m/L, where P_J is the largest k/w < n + 1/2 with k <= J.
So "no compatible family of K c-change functions in band n" is equivalent to the same statement on the
single grid (m, L) = P_J in lowest terms, J = K*c.

Usage:
  percc.py grid  n c [K]      # J = K*c (default K = 2*C(n,c) + 1), P_J and the grid that decides it
  percc.py max   m L c [W] [T]  # exact largest compatible family of c-change functions (CP-SAT, W workers,
                              # optional time limit T seconds; then status FEASIBLE and a bound)
  percc.py sat   m L c K      # independent check: is there a compatible family of K c-change functions?
                              # (CaDiCaL, one call per symmetry orbit of the forced member)
  percc.py table m L          # largest family in each class, and the cap 2*C(n,c)

Needs ortools (max), python-sat (sat), networkx (table).
"""
import itertools
import math
import sys
import time
from fractions import Fraction


def band(m, L):
    """The n with 2/(2n+1) < L/m <= 1/n (None outside the first bands)."""
    for n in range(1, 10 * m):
        if 2 * L * n + L > 2 * m and n * L <= m:
            return n
    return None


def grid_for(n, J):
    """Largest k/w < n + 1/2 with 1 <= k <= J, returned as (k, w) in lowest terms."""
    best = Fraction(0)
    for w in range(1, 2 * J + 2):
        k = min(J, (2 * n + 1) * w // 2 if ((2 * n + 1) * w) % 2 else (2 * n + 1) * w // 2 - 1)
        if k >= 1 and Fraction(k, w) > best:
            best = Fraction(k, w)
    return best.numerator, best.denominator


def functions(m, L, c):
    """All c-change strings at (m, L), generated from the change positions."""
    out = set()
    for P in itertools.combinations(range(m), c):
        gaps = [b - a for a, b in zip(P, P[1:])] + [P[0] + m - P[-1]]
        if min(gaps) < L:
            continue
        for v0 in (0, 1):
            s = [v0 ^ (sum(p <= i for p in P) & 1) for i in range(m)]
            if (0 in P) == (s[m - 1] == s[0]):  # a change at 0 means the wrap does not flip s[m-1] -> s[0]
                out.add(tuple(s))
    return sorted(out)


def compatible(a, b, L):
    d = [x ^ y for x, y in zip(a, b)]
    if all(d):
        return True
    best = cur = 0
    for x in d + d:
        cur = cur + 1 if x else 0
        best = max(best, cur)
    return best >= L


def orbits(V):
    """Orbits of the dihedral action (shift with complement, reflection) restricted to V."""
    idx = {v: i for i, v in enumerate(V)}
    seen, out = set(), []
    for v in V:
        if v in seen:
            continue
        orb = set()
        for r in (list(v), list(v)[::-1]):
            t = r[:]
            for _ in range(2 * len(t)):
                orb.add(tuple(t))
                t = t[1:] + [1 - t[0]]
        orb &= set(idx)
        seen |= orb
        out.append(sorted(idx[o] for o in orb))
    return out


def cpsat_max(V, L, workers, time_limit=None):
    from ortools.sat.python import cp_model
    N = len(V)
    md = cp_model.CpModel()
    x = [md.new_bool_var(f"x{i}") for i in range(N)]
    for i in range(N):
        for j in range(i + 1, N):
            if not compatible(V[i], V[j], L):
                md.add_bool_or([x[i].Not(), x[j].Not()])
    md.maximize(sum(x))
    s = cp_model.CpSolver()
    s.parameters.num_workers = workers
    s.parameters.symmetry_level = 4
    if time_limit:
        s.parameters.max_time_in_seconds = time_limit
    st = s.solve(md)
    fam = [V[i] for i in range(N) if s.value(x[i])]
    return s.status_name(st), int(s.objective_value), int(s.best_objective_bound), fam


def sat_exists(V, L, K):
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver
    N = len(V)
    inc = [[-(i + 1), -(j + 1)] for i in range(N) for j in range(i + 1, N) if not compatible(V[i], V[j], L)]
    card = CardEnc.atleast(lits=list(range(1, N + 1)), bound=K, top_id=N, encoding=EncType.seqcounter).clauses
    orbs = orbits(V)
    for k, O in enumerate(orbs):
        # every family can be moved to contain the least member of its first orbit (in this fixed order)
        cl = inc + card + [[O[0] + 1]] + [[-(i + 1)] for prev in orbs[:k] for i in prev]
        with Solver(name="cadical153", bootstrap_with=cl) as s:
            if s.solve():
                model = set(l for l in s.get_model() if l > 0)
                return True, [V[i] for i in range(N) if i + 1 in model]
    return False, len(orbs)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "grid":
        n, c = int(sys.argv[2]), int(sys.argv[3])
        K = int(sys.argv[4]) if len(sys.argv) > 4 else 2 * math.comb(n, c) + 1
        k, w = grid_for(n, K * c)
        print(f"n={n} c={c} K={K}: J={K * c}, P_J={k}/{w}={k / w:.4f}; decided on the grid (m, L)=({k}, {w}): "
              f"{len(functions(k, w, c))} c-change functions")
    elif mode == "max":
        m, L, c = map(int, sys.argv[2:5])
        W = int(sys.argv[5]) if len(sys.argv) > 5 else 8
        T = float(sys.argv[6]) if len(sys.argv) > 6 else None
        V = functions(m, L, c)
        t = time.time()
        st, obj, bd, fam = cpsat_max(V, L, W, T)
        n = band(m, L)
        print(f"m={m} L={L} n={n} c={c} functions={len(V)} status={st} largest={obj} bound={bd} "
              f"cap 2C(n,c)={2 * math.comb(n, c) if n else '-'} ({time.time() - t:.0f}s)")
        print("family:", " ".join("".join(map(str, s)) for s in fam))
    elif mode == "sat":
        m, L, c, K = map(int, sys.argv[2:6])
        V = functions(m, L, c)
        t = time.time()
        ok, info = sat_exists(V, L, K)
        if ok:
            print(f"m={m} L={L} c={c}: a compatible family of {K} exists:", " ".join("".join(map(str, s)) for s in info))
        else:
            print(f"m={m} L={L} c={c}: no compatible family of {K} ({len(V)} functions, {info} orbit cases UNSAT, "
                  f"{time.time() - t:.0f}s)")
    elif mode == "table":
        import networkx as nx
        m, L = map(int, sys.argv[2:4])
        n = band(m, L)
        top = n if n else m // L
        for c in range(1, top + 1, 2):
            V = functions(m, L, c)
            G = nx.Graph()
            G.add_nodes_from(range(len(V)))
            G.add_edges_from((i, j) for i in range(len(V)) for j in range(i + 1, len(V)) if compatible(V[i], V[j], L))
            print(f"m={m} L={L} n={n} c={c}: functions={len(V)} largest={nx.max_weight_clique(G, weight=None)[1]} "
                  f"cap={2 * math.comb(n, c) if n else '-'}", flush=True)
