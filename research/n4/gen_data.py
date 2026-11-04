#!/usr/bin/env python3
"""Regenerate GridSym.lean and AdjTree.lean from GridData.lean.

Usage: python3 gen_data.py Blumenthal/N4/GridData.lean OUTDIR

GridData.lean itself is produced by `sym_search.py --export` (the 528 strings at grid (22, 5),
ordered by degree, with rotation-orbit labels and representatives). None of these files needs to
be trusted: `GridFacts.lean` checks every fact used about them by kernel evaluation.
"""
import re
import sys

src, outdir = sys.argv[1], sys.argv[2]
gd = open(src).read()
grab = lambda name: [int(x) for x in re.search(rf"def {name} : List Nat := \[([^\]]*)\]", gd).group(1).split(",")]
masks, orbit, reps = grab("gridMasks"), grab("gridOrbit"), grab("gridReps")
N, M = len(masks), 44
FULL = (1 << M) - 1


def rot1(x):
    return ((x << 1) & FULL) | (x >> 43)


def compat(x, y):
    d = x ^ y
    r = d
    for _ in range(4):
        d = rot1(d)
        r &= d
    return r != 0


# GridSym: index permutation of a one-cell rotation, rotations needed to reach the orbit rep
idx = {x: i for i, x in enumerate(masks)}
pi = [idx[rot1(x)] for x in masks]
to_rep = []
for i in range(N):
    j, r = i, 0
    while j != reps[orbit[i]]:
        j, r = pi[j], r + 1
    to_rep.append(r)
with open(f"{outdir}/GridSym.lean", "w") as f:
    f.write("/-! Generated: index permutation of a one-cell rotation, and rotations to the orbit rep. -/\n\n")
    f.write("def gridRotIdx : List Nat := [" + ", ".join(map(str, pi)) + "]\n\n")
    f.write("def gridToRep : List Nat := [" + ", ".join(map(str, to_rep)) + "]\n")

# AdjTree: row of the vertex at bit b (vertex i = 527 - b), as a balanced tree
bit_of = lambda i: N - 1 - i
rows = [0] * N
for i in range(N):
    r = 0
    for j in range(N):
        if compat(masks[i], masks[j]):
            r |= 1 << bit_of(j)
    rows[bit_of(i)] = r


def emit(lo, hi):
    if hi <= lo + 1:
        return f"(.leaf {rows[lo]})"
    mid = (lo + hi) // 2
    return f"(.node {mid} {emit(lo, mid)} {emit(mid, hi)})"


with open(f"{outdir}/AdjTree.lean", "w") as f:
    f.write("inductive RowTree where\n  | leaf (row : Nat)\n  | node (split : Nat) (l r : RowTree)\n\n"
            "/-- `get t v`: row of vertex `v` -/\ndef RowTree.get : RowTree → Nat → Nat\n"
            "  | .leaf r, _ => r\n  | .node s l r, v => if v < s then l.get v else r.get v\n\n"
            "def adjTree : RowTree :=\n  " + emit(0, N) + "\n")
print("wrote GridSym.lean and AdjTree.lean")
