"""Exact largest compatible family for (R) at fixed (m, L) with OR-tools CP-SAT
(docs/STEP5-NOTES.md, Attempt 3; same discretisation as relaxation.py).

Model: x_f in {0,1} per valid sign function, AtMostOne over each clique of a greedy edge-clique cover of
the incompatibility graph, objective max sum x_f (or feasibility sum >= K). CP-SAT proves optimality,
so an OPTIMAL value of 2^n is an exact verification of (R) at (m, L). CP-SAT detects the dihedral symmetry
(shift with complement, reflection) itself.

Usage: relaxation_cpsat.py m L [K] [workers] [time_limit_s]
Needs ortools.
"""
import itertools
import sys
import time

from ortools.sat.python import cp_model

from relaxation import compatible
from relaxation_sat import functions


def clique_cover(N, inc):
    """Greedy cover of the incompatibility edges by cliques."""
    uncovered = {(i, j) for i in range(N) for j in range(i + 1, N) if inc[i][j]}
    adj = [set(j for j in range(N) if j != i and inc[i][j]) for i in range(N)]
    cliques = []
    while uncovered:
        i, j = min(uncovered)
        c = [i, j]
        cand = adj[i] & adj[j]
        # prefer candidates that cover many still-uncovered edges
        while cand:
            k = max(cand, key=lambda k: sum(((min(k, a), max(k, a)) in uncovered) for a in c))
            c.append(k)
            cand &= adj[k]
        cliques.append(c)
        for a, b in itertools.combinations(sorted(c), 2):
            uncovered.discard((a, b))
    return cliques


def main():
    m, L = int(sys.argv[1]), int(sys.argv[2])
    K = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != "max" else None
    W = int(sys.argv[4]) if len(sys.argv) > 4 else 16
    T = float(sys.argv[5]) if len(sys.argv) > 5 else 1e9
    t0 = time.time()
    V = functions(m, L)
    N = len(V)
    inc = [[i != j and not compatible(V[i], V[j], L) for j in range(N)] for i in range(N)]
    cl = clique_cover(N, inc)
    md = cp_model.CpModel()
    x = [md.new_bool_var(f"x{i}") for i in range(N)]
    for c in cl:
        md.add_at_most_one(x[i] for i in c)
    if K is None:
        md.maximize(sum(x))
    else:
        md.add(sum(x) >= K)
    s = cp_model.CpSolver()
    s.parameters.num_workers = W
    s.parameters.max_time_in_seconds = T
    s.parameters.symmetry_level = 4  # let CP-SAT detect the dihedral symmetry itself
    s.parameters.log_search_progress = True
    s.parameters.log_to_stdout = True
    print(f"m={m} L={L} L/m={L/m:.4f} functions={N} cliques={len(cl)}", flush=True)
    st = s.solve(md)
    print("status", s.status_name(st), "objective", s.objective_value if K is None else "-",
          "bound", s.best_objective_bound if K is None else "-", f"time {time.time() - t0:.1f}s")
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        print("family:", " ".join("".join(map(str, V[i])) for i in range(N) if s.value(x[i])))


if __name__ == "__main__":
    main()
