#!/usr/bin/env python3
"""Finite checks of the minimum-checkpoint-set statements, not gate-count proofs.

For random maps on N <= 10 states and window lengths K <= 5 this compares
the brute-force minimum K-checkpoint set with (a) the component formula of
the paper (minimum over the cycle options of in-forest packing numbers) and
(b) the exact table algorithm (tree greedy followed by circular-arc stabbing).
It also checks the in-forest min-max duality against brute-force packings.
"""

from itertools import combinations
from random import Random


def trajectories(f, k):
    """All K-trajectories: lists of K distinct consecutive states."""
    result = []
    for x in range(len(f)):
        path, seen, y = [], set(), x
        while len(path) < k and y not in seen:
            seen.add(y)
            path.append(y)
            y = f[y]
        if len(path) == k:
            result.append(frozenset(path))
    return result


def brute_cover(sets, universe):
    """Minimum number of points of the universe hitting every set."""
    sets = list(set(sets))
    for size in range(len(universe) + 1):
        for chosen in combinations(universe, size):
            c = set(chosen)
            if all(s & c for s in sets):
                return size
    raise AssertionError("no cover")


def brute_packing(sets):
    """Maximum number of pairwise disjoint sets."""
    sets = list(set(sets))
    best = 0

    def go(i, used, count):
        nonlocal best
        best = max(best, count)
        if count + len(sets) - i <= best:
            return
        for j in range(i, len(sets)):
            if not (sets[j] & used):
                go(j + 1, used | sets[j], count + 1)

    go(0, frozenset(), 0)
    return best


def forest_greedy(succ, vertices, req):
    """Greedy cover of required paths in an in-forest.

    succ[v] is the successor of v inside the forest or None; a required path
    ends at v and has at least req[v] vertices.  Returns the greedy set,
    which by the duality lemma is a minimum cover and has the size of a
    maximum packing.
    """
    preds = {v: [] for v in vertices}
    for v in vertices:
        if succ[v] is not None:
            preds[succ[v]].append(v)
    height = {}

    def h(v):
        if v not in height:
            height[v] = 1 + max((h(u) for u in preds[v]), default=0)
        return height[v]

    chosen, d = set(), {}
    for v in sorted(vertices, key=h):
        d[v] = 1 + max((d[u] for u in preds[v] if u not in chosen), default=0)
        if d[v] >= req[v]:
            chosen.add(v)
    return chosen


def required_paths(succ, vertices, req):
    """Minimal required paths: exactly req[v] vertices ending at v."""
    preds = {v: [] for v in vertices}
    for v in vertices:
        if succ[v] is not None:
            preds[succ[v]].append(v)
    result = []

    def back(path):
        if len(path) == req[path[0]]:
            result.append(frozenset(path))
            return
        for u in preds[path[-1]]:
            back(path + [u])

    for v in vertices:
        back([v])
    return result


def components(f):
    n = len(f)
    comp = [None] * n
    cycles = []
    for x in range(n):
        if comp[x] is not None:
            continue
        path, pos, y = [], {}, x
        while comp[y] is None and y not in pos:
            pos[y] = len(path)
            path.append(y)
            y = f[y]
        if comp[y] is None:
            label = len(cycles)
            cycles.append(path[pos[y]:])
        else:
            label = comp[y]
        for z in path:
            comp[z] = label
    return comp, cycles


def formula_opt(f, k):
    """Sum over components of the minimum over cycle options of packings."""
    comp, cycles = components(f)
    total = 0
    for label, cycle in enumerate(cycles):
        q = [v for v in range(len(f)) if comp[v] == label]
        ell = len(cycle)
        options = []
        window = cycle[:k] if ell >= k else cycle
        for c in window:
            verts = [v for v in q if v != c]
            succ = {v: (f[v] if f[v] != c else None) for v in verts}
            req = {v: k for v in verts}
            options.append(1 + len(forest_greedy(succ, verts, req)))
        if ell < k:
            zset = set(cycle)
            verts = [v for v in q if v not in zset]
            succ = {v: (f[v] if f[v] not in zset else None) for v in verts}
            req = {v: (k - ell if f[v] in zset else k) for v in verts}
            options.append(len(forest_greedy(succ, verts, req)))
        total += min(options)
    return total


def line_stab(arcs, ell):
    """Greedy stabbing of intervals [a, b] on 0..ell-1 (already cut)."""
    count, last = 0, -1
    for a, b in sorted(arcs, key=lambda ab: ab[1]):
        if a > last:
            count += 1
            last = b
    return count


def circle_stab(arcs, ell):
    """Minimum points on a cycle of ell positions stabbing the given arcs.

    An arc is (start, width) covering start, ..., start+width-1 mod ell,
    with width <= ell.  Some optimal set meets the shortest arc; for each
    point p of it, cut the circle at p and run the line greedy.
    """
    if not arcs:
        return 0
    s, w = min(arcs, key=lambda a: a[1])
    best = None
    for off in range(w):
        p = (s + off) % ell
        rest = []
        for a, width in arcs:
            if (p - a) % ell < width:
                continue
            start = (a - p) % ell
            rest.append((start, start + width - 1))
        value = 1 + line_stab(rest, ell)
        best = value if best is None else min(best, value)
    return best


def table_opt(f, k):
    """Exact table algorithm: tree greedy, then circular-arc stabbing."""
    comp, cycles = components(f)
    on_cycle = {v for cycle in cycles for v in cycle}
    tree = [v for v in range(len(f)) if v not in on_cycle]
    succ = {v: (f[v] if f[v] not in on_cycle else None) for v in tree}
    req = {v: k for v in tree}
    picks = forest_greedy(succ, tree, req)
    preds = {v: [] for v in tree}
    for v in tree:
        if succ[v] is not None:
            preds[succ[v]].append(v)
    d = {}
    for v in sorted(tree, key=lambda v: -depth(f, v, on_cycle)):
        d[v] = 0 if v in picks else 1 + max((d[u] for u in preds[v]), default=0)
    total = len(picks)
    for cycle in cycles:
        ell = len(cycle)
        arcs = []
        for i, v in enumerate(cycle):
            a = max((d[u] for u in tree if f[u] == v), default=0)
            width = k - a
            if width <= ell:
                arcs.append((i, width))
        total += circle_stab(arcs, ell)
    return total


def depth(f, v, on_cycle):
    count = 0
    while v not in on_cycle:
        v = f[v]
        count += 1
    return count


def random_map(rng, n):
    kind = rng.randrange(3)
    if kind == 0:
        return [rng.randrange(n) for _ in range(n)]
    if kind == 1:
        perm = list(range(n))
        rng.shuffle(perm)
        return perm
    # Long tails into a few short cycles.
    f = [rng.randrange(max(1, x)) if x else 0 for x in range(n)]
    cycle = rng.sample(range(n), rng.randint(1, min(3, n)))
    for i, c in enumerate(cycle):
        f[c] = cycle[(i + 1) % len(cycle)]
    return f


def check_duality(rng, trials):
    for _ in range(trials):
        n = rng.randint(1, 9)
        succ = {v: (rng.randrange(v) if v and rng.random() < 0.85 else None)
                for v in range(n)}
        verts = list(range(n))
        kk = rng.randint(1, 4)
        req = {v: rng.randint(1, kk) for v in verts}
        paths = required_paths(succ, verts, req)
        greedy = forest_greedy(succ, verts, req)
        assert all(p & greedy for p in paths)
        cover = brute_cover(paths, verts)
        pack = brute_packing(paths)
        assert len(greedy) == cover == pack, (succ, req, greedy, cover, pack)


def main():
    rng = Random(20261017)
    check_duality(rng, 400)
    count = 0
    for _ in range(1900):
        n = rng.randint(1, 10)
        f = random_map(rng, n)
        k = rng.randint(1, 5)
        brute = brute_cover(trajectories(f, k), list(range(n)))
        assert formula_opt(f, k) == brute, (f, k)
        assert table_opt(f, k) == brute, (f, k)
        count += 1
    print("PASS: minimum-checkpoint-set checks succeeded.")
    print("Seed: 20261017")
    print("forest duality instances: 400")
    print(f"maps (N <= 10, K <= 5): {count:,}")
    print("Finite checks do not establish complexity bounds or historical novelty.")


if __name__ == "__main__":
    main()
