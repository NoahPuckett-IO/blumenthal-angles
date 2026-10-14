"""Exhaustive check of the aggregate Kraft certificate over arc colourings.
For Q and u: maximise sum_q 2^{nu(q)} over all partitions of RP^1 into n+1 half-open arcs of width <= lam,
where nu(q) = number of arcs containing no line direction of q.  A certificate for F(Q) <= 2^n needs >= 2F.
Groupings of the sorted line directions into consecutive groups are enumerated; feasibility of realising
a grouping with <= n+1 arcs is an LP (each group's arc may extend r_t right / l_t left with r_t + l_t <= lam - span_t,
gap t needs r_t + l_{t+1} >= G_t - e_t*lam where e_t = number of empty arcs placed in gap t)."""
import sys, math, itertools
import numpy as np
from scipy.optimize import linprog

EPS = 1e-9

def analyse(Q, u):
    lam = 2*math.pi/u; n = int(math.floor(u/2)); A = n+1; s = len(Q)
    lines = []
    for i in range(s):
        for j in range(i+1, s):
            d = math.atan2(Q[j][1]-Q[i][1], Q[j][0]-Q[i][0]) % math.pi
            lines.append((d, i, j))
    lines.sort(); M = len(lines); pos = [l[0] for l in lines]
    ks = []; F = 0
    for q in range(s):
        ds = sorted(l[0] for l in lines if q in (l[1], l[2]))
        gaps = [ds[t+1]-ds[t] for t in range(len(ds)-1)] + [ds[0]+math.pi-ds[-1]]
        k = sum(max(int(math.floor(g/lam + 1e-12))-1, 0) for g in gaps); ks.append(k); F += 2**k
    best = -1; bestinfo = None
    for g in range(1, A+1):
        for starts in itertools.combinations(range(M), g):
            groups = []
            ok = True
            for t in range(g):
                a = starts[t]
                idx = list(range(a, starts[t+1])) if t+1 < g else list(range(a, M)) + list(range(0, starts[0]))
                lo, hi = pos[idx[0]], pos[idx[-1]]
                span = (hi - lo) % math.pi
                if span >= lam - EPS: ok = False; break
                groups.append((idx, lo, hi, span))
            if not ok: continue
            if g == 1:
                gl = [math.pi - groups[0][3]]
            else:
                gl = [((groups[(t+1) % g][1] - groups[t][2]) % math.pi) for t in range(g)]
            # objective first (cheap) -- skip if cannot beat best
            val = 0
            for q in range(s):
                touched = sum(1 for gr in groups if any(q in (lines[t][1], lines[t][2]) for t in gr[0]))
                val += 2**(A - touched)
            if val <= best: continue
            # feasibility: exists e (sum e <= A-g) and r,l satisfying constraints
            feas = False
            for e in itertools.product(range(A-g+1), repeat=g):
                if sum(e) > A - g: continue
                # variables r_0..r_{g-1}, l_0..l_{g-1} >= 0
                Aub = []; bub = []
                for t in range(g):
                    row = [0]*(2*g); row[t] = 1; row[g+t] = 1; Aub.append(row); bub.append(lam - groups[t][3] - EPS)
                    row = [0]*(2*g); row[t] = -1; row[g+(t+1) % g] = -1; Aub.append(row); bub.append(-(gl[t] - e[t]*lam))
                    # gap must stay a gap: r_t + l_{t+1} <= G_t (cuts lie inside the gap) and r_t < G_t etc.
                    row = [0]*(2*g); row[t] = 1; row[g+(t+1) % g] = 1; Aub.append(row); bub.append(gl[t] - EPS)
                res = linprog(np.zeros(2*g), A_ub=Aub, b_ub=bub, bounds=[(0, None)]*(2*g), method="highs")
                if res.status == 0: feas = True; break
            if feas:
                best = val; bestinfo = ([len(gr[0]) for gr in groups], e)
    return F, ks, best, bestinfo, n

if __name__ == "__main__":
    u = float(sys.argv[1]); pts = [tuple(map(float, l.split())) for l in open(sys.argv[2]) if l.strip()]
    F, ks, best, info, n = analyse(pts, u)
    print(f"u={u} s={len(pts)} k={ks} F={F}; max over arc partitions of sum 2^nu = {best}; "
          f"certificate needs >= 2F = {2*F}; Kraft cap 2^(n+1) = {2**(n+1)}; best grouping {info}")
