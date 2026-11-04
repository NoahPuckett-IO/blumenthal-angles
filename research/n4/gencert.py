#!/usr/bin/env python3
"""Generate clique-bound certificates for Cert.lean, using the exact Lean adjacency rows.

Vertices are Lean bit positions 0..527 (bit = 527 - index in gridMasks).
Usage: gencert.py ROWS GRIDDATA OUTDIR [--case o] [--size-test]
"""
import re
import sys

rows_file, griddata, outdir = sys.argv[1:4]
adj = [int(x) for x in open(rows_file).read().split()]
N = len(adj)
gd = open(griddata).read()
orbit = [int(x) for x in re.search(r"def gridOrbit : List Nat := \[([^\]]*)\]", gd).group(1).split(",")]
reps = [int(x) for x in re.search(r"def gridReps : List Nat := \[([^\]]*)\]", gd).group(1).split(",")]
bitOf = lambda i: N - 1 - i
pc = lambda x: bin(x).count("1")


def caseP(o):
    m = 0
    for i, x in enumerate(orbit):
        if x >= o:
            m |= 1 << bitOf(i)
    return adj[bitOf(reps[o])] & m


def colour(P):
    vs = [v for v in range(N) if P >> v & 1]
    vs.sort(key=lambda v: (-pc(adj[v] & P), v))
    classes = []
    for v in vs:
        for c in classes:
            if not (adj[v] & c[0]):
                c[0] |= 1 << v
                c[1].append(v)
                break
        else:
            classes.append([1 << v, [v]])
    return [c[1] for c in classes]


class Node:
    __slots__ = ("P", "k", "cls", "kids", "size")


def build(P, k):
    n = Node()
    n.P, n.k = P, k
    n.cls = colour(P)
    n.kids = []
    assert k > 0, "found a clique"
    if len(n.cls) >= k:
        Pp = P
        for v in [v for c in n.cls[k - 1:] for v in c]:
            n.kids.append(build(Pp & adj[v], k - 1))
            Pp &= ~(1 << v)
    n.size = 1 + sum(c.size for c in n.kids)
    return n


def lean_cert(n):
    cls = "[" + ", ".join("[" + ", ".join(map(str, c)) + "]" for c in n.cls) + "]"
    kids = "[" + ", ".join(lean_cert(c) for c in n.kids) + "]"
    return f"(.node {cls} {kids})"


if __name__ == "__main__":
    import os
    if "--case" in sys.argv:
        o = int(sys.argv[sys.argv.index("--case") + 1])
        root = build(caseP(o), 8)
        print("case", o, "nodes", root.size)
        if "--size-test" in sys.argv:
            # emit one theorem per subtree of the root, for memory/time measurement
            for j, kid in enumerate(root.kids):
                print(j, kid.size)
