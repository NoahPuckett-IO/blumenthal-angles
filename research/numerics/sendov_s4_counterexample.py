# Explicit 4-centre configuration beating Sendov's asserted s=4 maximum (Lemma 4.1, case c.2).
# n = 3, u = 15/2 (delta = u/2 - n = 3/4 >= 1/2), alpha = (1 - 2/u) pi = (11/15) pi, lam = 2pi/u = (4/15) pi.
# Sendov asserts: for s = 4 and 1/2 <= delta < 1 the max of |P| is 2^n + 2^(n-3) = 9.
# Here: o1=(-1,0), o2=(1,0), o3a=(0,1/2), o3b=(0,1/2+1/100); k = (2,2,0,0) -> 4+4+1+1 = 10.
from mpmath import mp, mpf, atan2, pi, floor
mp.dps = 50
u = mpf(15)/2; lam = 2*pi/u; amax = pi - lam
Q = [(mpf(-1),mpf(0)), (mpf(1),mpf(0)), (mpf(0),mpf(1)/2), (mpf(0),mpf(1)/2+mpf(1)/100)]
def ang(v): return atan2(v[1], v[0])
worst = mpf(0)
for i,q in enumerate(Q):
    for j,a in enumerate(Q):
        for l,b in enumerate(Q):
            if len({i,j,l})<3 or j>l: continue
            t = abs(ang((a[0]-q[0],a[1]-q[1])) - ang((b[0]-q[0],b[1]-q[1])))
            if t > pi: t = 2*pi - t
            worst = max(worst, t)
print("max angle / pi =", worst/pi, " bound (1-2/u) =", 1-2/u, " slack/pi =", (amax-worst)/pi)
F = 0
for i,q in enumerate(Q):
    ds = sorted([ang((a[0]-q[0],a[1]-q[1])) % pi for j,a in enumerate(Q) if j!=i])
    gaps = [ds[t+1]-ds[t] for t in range(len(ds)-1)] + [ds[0]+pi-ds[-1]]
    k = sum(max(int(floor(g/lam))-1,0) for g in gaps)
    # distance of each gap/lam to the nearest integer, to show floors are robust
    rob = min(abs(g/lam - floor(g/lam+mpf(1)/2)) for g in gaps)
    print(f"o{i+1}: gaps/lam =", [float(g/lam) for g in gaps], " k =", k, " min dist to integer:", float(rob))
    F += 2**k
print("F =", F, "; Sendov's asserted s=4 maximum = 9; Lemma 4.1 final bound 2^n+2^(n-2) = 10")
