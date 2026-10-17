#!/usr/bin/env python3
"""Numerical evidence for the random-mapping hypotheses of the black-box section.

This script is not a proof.  For a few uniformly random maps f on N points it
checks the phase identities (P1) and (P2), the rho-length bound of Lemma L0,
and reports the ratios bounded by the hypotheses L1 and L2.  Here kappa(v) is
the first time at which the trajectory of v visits the least state of its
cycle.

  L1: |f^{-j}(w)| <= C1 (j+1) ln N   for all w and 0 <= j <= J,
  L2: #{v with a given cycle : kappa(v) = k} <= C2 sqrt(N) ln N.

The assertions use C1 = C2 = 1.  The hypotheses in the paper only ask for some
absolute constants and failure probability at most 1/N; a simulation of this
size says nothing about such small tails.
"""

from math import log, sqrt
from random import Random


def structure(f):
    """Return cyclic flags, depth, root, cycle id, cycle length and position."""
    n = len(f)
    indeg = [0] * n
    for v in range(n):
        indeg[f[v]] += 1
    cyclic = [True] * n
    stack = [v for v in range(n) if indeg[v] == 0]
    while stack:
        v = stack.pop()
        cyclic[v] = False
        w = f[v]
        indeg[w] -= 1
        if indeg[w] == 0:
            stack.append(w)
    cycle_id = [-1] * n
    pos = [0] * n
    lengths = []
    for v in range(n):
        if cyclic[v] and cycle_id[v] < 0:
            cyc = [v]
            u = f[v]
            while u != v:
                cyc.append(u)
                u = f[u]
            k = cyc.index(min(cyc))
            cyc = cyc[k:] + cyc[:k]
            for i, u in enumerate(cyc):
                cycle_id[u] = len(lengths)
                pos[u] = i
            lengths.append(len(cyc))
    preimages = [[] for _ in range(n)]
    for v in range(n):
        if not cyclic[v]:
            preimages[f[v]].append(v)
    depth = [0] * n
    root = list(range(n))
    frontier = [v for v in range(n) if cyclic[v]]
    while frontier:
        nxt = []
        for w in frontier:
            for v in preimages[w]:
                depth[v] = depth[w] + 1
                root[v] = root[w]
                cycle_id[v] = cycle_id[w]
                nxt.append(v)
        frontier = nxt
    return cyclic, depth, root, cycle_id, lengths, pos


def check(n, seed, max_j):
    rng = Random(seed)
    f = [rng.randrange(n) for _ in range(n)]
    cyclic, depth, root, cid, lengths, pos = structure(f)
    kappa = [depth[v] + (lengths[cid[v]] - pos[root[v]]) % lengths[cid[v]]
             for v in range(n)]

    # P1: kappa decreases by one along f off the cycles.
    for v in range(n):
        if not cyclic[v]:
            assert kappa[f[v]] == kappa[v] - 1
    # P2: for T >= depth(v), f^T(v) is the cyclic point at (T - kappa(v)) mod ell.
    by_pos = {}
    for v in range(n):
        if cyclic[v]:
            by_pos[(cid[v], pos[v])] = v
    for v in rng.sample(range(n), 200):
        ell = lengths[cid[v]]
        steps = depth[v] + rng.randrange(3 * ell + 1)
        u = v
        for _ in range(steps):
            u = f[u]
        assert u == by_pos[(cid[v], (steps - kappa[v]) % ell)]

    # L0: every rho length is at most 2 sqrt(N ln N).
    rho = max(depth[v] + lengths[cid[v]] for v in range(n))
    assert rho <= 2 * sqrt(n * log(n)), (n, seed, rho)

    # L1: level sizes of in-trees, |f^{-j}(w)| for 0 <= j <= max_j.
    counts = [1] * n
    worst1 = 0.0
    for j in range(1, max_j + 1):
        new = [0] * n
        for v in range(n):
            new[f[v]] += counts[v]
        counts = new
        worst1 = max(worst1, max(counts) / ((j + 1) * log(n)))
    assert worst1 <= 1.0, (n, seed, worst1)

    # L2: classes of equal kappa with a common cycle.
    classes = {}
    for v in range(n):
        key = (cid[v], kappa[v])
        classes[key] = classes.get(key, 0) + 1
    biggest = max(classes.values())
    worst2 = biggest / (sqrt(n) * log(n))
    assert worst2 <= 1.0, (n, seed, worst2)
    return rho / sqrt(n * log(n)), worst1, biggest / sqrt(n), worst2


def main():
    print("N        seed  rho/sqrt(N lnN)  L1 ratio  L2 max/sqrtN  L2 ratio")
    for exponent in (12, 14, 16):
        n = 1 << exponent
        for seed in (1, 2):
            r0, r1, b2, r2 = check(n, seed, min(64, int(sqrt(n))))
            print(f"2^{exponent:<6} {seed:<5} {r0:15.3f}  {r1:8.3f}  {b2:12.3f}  {r2:8.3f}")
    print("Phase identities P1, P2 and bound L0 hold; L1, L2 ratios are at most 1.")


if __name__ == "__main__":
    main()
