"""Cover Lemma experiments (first band, u < 2n+1).

Notation. For a direction matrix W (W[p][q] = direction of the vector p->q in S^1) and an arc
A = [theta, theta+lam) of S^1, the 'cell' C(theta) is the set of points with no vector in A.
Then C(theta) and C(theta+pi) cover P, and every pair inside a cell has its line direction outside
[theta, theta+lam) mod pi.

Cover Lemma (conjecture): there is a theta such that the line directions inside C(theta) and inside
C(theta+pi) can each be covered by n-1 half-open lam-arcs. By the Erdos-Szekeres even-partition
bound, each cell then has at most 2^(n-1) points, so |P| <= 2^n.

Usage:
  cover_lemma.py local  u s trials maximize seed   # random local configurations (GC-expanded)
  cover_lemma.py real   u_build u cfg...           # realise centre configurations as real point sets
"""
import math
import random
import sys

TAU = 2 * math.pi


def ang(a, b):
    d = (a - b) % TAU
    return min(d, TAU - d)


# ---------- local configurations ----------

def local_violation(V, lam):
    s = len(V)
    v = 0.0
    for i in range(s):
        vs = [V[i][j] for j in range(s) if j != i]
        for a in range(len(vs)):
            for b in range(a + 1, len(vs)):
                t = ang(vs[a], vs[b]) - (math.pi - lam)
                if t > 0:
                    v += t
    return v


def kappa(V, i, lam):
    s = len(V)
    ds = sorted(V[i][j] % math.pi for j in range(s) if j != i)
    k = 0
    for t in range(len(ds)):
        g = (ds[t + 1] if t + 1 < len(ds) else ds[0] + math.pi) - ds[t]
        k += max(int(math.floor(g / lam + 1e-12)) - 1, 0)
    return k


def weight(V, lam):
    return sum(2 ** kappa(V, i, lam) for i in range(len(V)))


def random_local(s, lam, maximize, rng, iters=20000):
    """Anneal an antisymmetric direction matrix satisfying the per-point angle bound."""
    V = [[None] * s for _ in range(s)]
    for i in range(s):
        for j in range(i + 1, s):
            V[i][j] = rng.uniform(0, TAU)
            V[j][i] = (V[i][j] + math.pi) % TAU
    cur = local_violation(V, lam)
    curF = weight(V, lam) if cur == 0 else 0
    T = 1.0
    for it in range(iters):
        i, j = rng.sample(range(s), 2)
        old = V[i][j]
        V[i][j] = (old + rng.gauss(0, 0.3)) % TAU
        V[j][i] = (V[i][j] + math.pi) % TAU
        nv = local_violation(V, lam)
        nF = weight(V, lam) if nv == 0 else 0
        so = -1000 * cur + (curF if maximize else 0)
        sn = -1000 * nv + (nF if maximize else 0)
        if sn >= so or rng.random() < math.exp((sn - so) / T):
            cur, curF = nv, nF
        else:
            V[i][j] = old
            V[j][i] = (old + math.pi) % TAU
        T = max(T * 0.9995, 1e-3)
        if not maximize and cur == 0 and it > 2000:
            break
    return V if cur == 0 else None


def internal_lines(dirs_mod_pi, lam):
    """A maximal lam-separated set of lines at distance >= lam from the given lines (Sendov's clusters)."""
    ds = sorted(dirs_mod_pi)
    out = []
    for t in range(len(ds)):
        a = ds[t]
        b = ds[t + 1] if t + 1 < len(ds) else ds[0] + math.pi
        x = a + lam
        while x <= b - lam + 1e-12:
            out.append(x % math.pi)
            x += lam
    return out


def expand(V, lam):
    """Replace each centre by a perfect cluster of 2^kappa points (exact generalised directions)."""
    s = len(V)
    S = [internal_lines([V[i][j] % math.pi for j in range(s) if j != i], lam) for i in range(s)]
    pts = [(i, a) for i in range(s) for a in range(2 ** len(S[i]))]
    N = len(pts)
    W = [[None] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if a == b:
                continue
            (i, x), (j, y) = pts[a], pts[b]
            if i != j:
                W[a][b] = V[i][j]
            else:
                d = x ^ y
                lvl = (d & -d).bit_length() - 1
                W[a][b] = S[i][lvl] if (x >> lvl) & 1 == 0 else (S[i][lvl] + math.pi) % TAU
    return W


# ---------- real configurations ----------

def realise(Q, lam, r0=1e-3, ratio=1e-3, rng=random):
    """Actual point set approximating the GC expansion of the centre set Q."""
    s = len(Q)
    pts = []
    for i, q in enumerate(Q):
        S = internal_lines([math.atan2(Q[j][1] - q[1], Q[j][0] - q[0]) % math.pi for j in range(s) if j != i], lam)
        rng.shuffle(S)
        for addr in range(2 ** len(S)):
            x, y = q
            r = r0
            for lvl, d in enumerate(S):
                sg = 1 if (addr >> lvl) & 1 else -1
                x += sg * r * math.cos(d) / 2
                y += sg * r * math.sin(d) / 2
                r *= ratio
            pts.append((x, y))
    return pts


def directions(P):
    N = len(P)
    return [[math.atan2(P[j][1] - P[i][1], P[j][0] - P[i][0]) % TAU if i != j else None for j in range(N)]
            for i in range(N)]


def max_angle(W):
    N = len(W)
    return max(ang(W[i][a], W[i][b]) for i in range(N) for a in range(N) for b in range(N)
               if len({i, a, b}) == 3)


# ---------- the lemma ----------

def cell(W, theta, lam):
    """Points with no vector in [theta, theta+lam)."""
    N = len(W)
    return [p for p in range(N)
            if not any((W[p][q] - theta) % TAU < lam - 1e-12 for q in range(N) if q != p)]


def cover_number(lines, lam):
    """Least number of half-open lam-arcs covering a finite subset of RP^1 = R/piZ."""
    ds = sorted(set(round(d % math.pi, 10) for d in lines))
    m = len(ds)
    if m == 0:
        return 0
    best = m
    for start in range(m):
        cnt, i = 0, 0
        while i < m:
            x = ds[(start + i) % m] + (math.pi if start + i >= m else 0)
            cnt += 1
            while i < m and ds[(start + i) % m] + (math.pi if start + i >= m else 0) - x < lam - 1e-12:
                i += 1
        best = min(best, cnt)
    return best


def cell_cover(W, theta, lam):
    c = cell(W, theta, lam)
    return cover_number([W[p][q] for p in c for q in c if p != q], lam), len(c)


def cover_lemma(W, lam, n, K=1440):
    """Return (holds, fraction of theta in S^1 whose cell C(theta) needs >= n arcs)."""
    bad = [cell_cover(W, TAU * k / K, lam)[0] >= n for k in range(K)]
    holds = any(not bad[k] and not bad[(k + K // 2) % K] for k in range(K))
    return holds, sum(bad) / K


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "local":
        u, s, trials, mx, seed = float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
        lam, n = TAU / u, int(u // 2)
        assert u < 2 * n + 1, "first band only"
        rng = random.Random(seed)
        fails = done = 0
        worst = 0.0
        for t in range(trials):
            V = random_local(s, lam, mx, rng)
            if V is None:
                continue
            W = expand(V, lam)
            ok, bf = cover_lemma(W, lam, n, K=720)
            done += 1
            fails += not ok
            worst = max(worst, bf)
            print(f"trial {t}: N={len(W)} F={weight(V, lam)} cover_lemma={ok} bad_fraction={bf:.3f}", flush=True)
        print(f"local u={u} s={s}: {fails} failures of {done}; worst bad fraction {worst:.3f}")
    else:
        u_build, u = float(sys.argv[2]), float(sys.argv[3])
        lam, n = TAU / u, int(u // 2)
        rng = random.Random(2)
        for f in sys.argv[4:]:
            Q = [tuple(map(float, l.split())) for l in open(f) if l.strip()]
            W = directions(realise(Q, TAU / u_build, rng=rng))
            if max_angle(W) > math.pi - lam:
                print(f, "realisation exceeds the angle bound; skipped")
                continue
            ok, bf = cover_lemma(W, lam, n)
            print(f"{f}: N={len(W)} cover_lemma={ok} bad_fraction={bf:.3f}", flush=True)
