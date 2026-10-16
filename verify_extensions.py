#!/usr/bin/env python3
"""Independent finite checks of the added graph statements, not gate-count proofs."""

from collections import Counter
from itertools import product
from math import factorial, lcm
from random import Random


def orbit(f, x):
    positions, path = {}, []
    while x not in positions:
        positions[x] = len(path)
        path.append(x)
        x = f[x]
    mu = positions[x]
    cycle = path[mu:]
    c = min(cycle)
    return path, mu, len(cycle), c, (-path.index(c)) % len(cycle)


def iterate(info, t):
    path, mu, period, _, _ = info
    return path[t] if t < len(path) else path[mu + (t - mu) % period]


def prefix(f, x, count):
    result = []
    for _ in range(count):
        result.append(x)
        x = f[x]
    return result


def packed_checkpoints(f, length):
    remaining, marked = set(range(len(f))), set()
    while True:
        for x in sorted(remaining):
            path = prefix(f, x, length)
            if len(set(path)) == length and set(path) <= remaining:
                marked.add(path[-1])
                remaining.difference_update(path)
                break
        else:
            return marked


def active_checkpoints(f, infos, length):
    deep = [v for v, info in enumerate(infos) if info[1] >= length]
    residue = min(range(length), key=lambda r: sum(infos[v][1] % length == r for v in deep))
    marked = {v for v in deep if infos[v][1] % length == residue}
    long_cycle_vertices = set()
    for c in {info[3] for info in infos}:
        period = infos[c][2]
        if period >= length:
            cycle = prefix(f, c, period)
            long_cycle_vertices.update(cycle)
            marked.update(cycle[::length])
    return marked, len(deep) + len(long_cycle_vertices)


def labels_from_prefix(f, infos, marked, x, length):
    path = prefix(f, x, 2 * length + 1)
    for d, h in enumerate(path):
        if h in marked:
            _, _, period, c, phase = infos[h]
            return period, c, (phase - d) % period
    records = sorted((state, i) for i, state in enumerate(path))
    pairs = [(j, i) for (a, i), (b, j) in zip(records, records[1:]) if a == b]
    j, i = min(pairs)
    p = min(range(i, j), key=path.__getitem__)
    return j - i, path[p], (-p) % (j - i)


def check_map(f, counts):
    n = len(f)
    infos = [orbit(f, x) for x in range(n)]
    projection = [iterate(info, factorial(n)) for info in infos]
    counts["maps"] += 1
    for length in range(1, n + 1):
        marked = packed_checkpoints(f, length)
        assert len(marked) * length <= n
        active, q = active_checkpoints(f, infos, length)
        assert len(active) * length <= 2 * q
        for x in range(n):
            short = prefix(f, x, length)
            assert len(set(short)) < length or set(prefix(f, x, 2 * length)) & marked
            assert labels_from_prefix(f, infos, marked, x, length) == infos[x][2:]
            long = prefix(f, x, 3 * length + 1)
            assert set(long) & active or len(set(long)) < len(long)
            counts["packing, labels, active coverage"] += 1
            path = prefix(f, x, 2 * length + 1)
            projected_path = prefix(f, projection[x], 2 * length + 1)
            if path[-1] == projected_path[-1]:
                depth = next(j for j, (a, b) in enumerate(zip(path, projected_path)) if a == b)
            else:
                candidates = [j + infos[h][1] for j, h in enumerate(path) if h in marked]
                assert candidates and all(d == infos[x][1] for d in candidates)
                depth = candidates[-1]
            assert depth == infos[x][1]
            counts["checkpoint-depth reconstructions"] += 1
    exponent = lcm(*range(1, n + 1))
    for x in range(n):
        projected = projection[x]
        assert projection[projected] == projected and infos[projected][1] == 0
        for t in (*range(2 * n + 1), (1 << 258) + 9, (1 << 521) + 31):
            normalized = t if t < n else n + (t - n) % infos[x][2]
            assert normalized < 2 * n
            assert iterate(infos[x], normalized) == iterate(infos[x], t)
            assert (iterate(infos[x], t) == iterate(infos[projected], t)) == (infos[x][1] <= t)
            counts["projection and time normalization"] += 1
        lo, hi = 0, n - 1
        while lo < hi:
            mid = (lo + hi) // 2
            z = iterate(infos[x], mid)
            if iterate(infos[z], exponent) == z:
                hi = mid
            else:
                lo = mid + 1
        assert lo == infos[x][1]
        for y in range(n):
            _, mx, period, cx, px = infos[x]
            _, my, _, cy, py = infos[y]
            if my:
                answer = mx - my if mx >= my and iterate(infos[x], mx - my) == y else None
            else:
                answer = mx + (py - px - mx) % period if cx == cy else None
            path = infos[x][0]
            expected = path.index(y) if y in path else None
            assert answer == expected
            counts["hitting-time pairs"] += 1
            return_period = infos[y][2] if infos[y][1] == 0 else 0
            actual_count = 0
            for t in range(2 * n + 2):
                scheduled = answer is not None and (
                    t == answer if return_period == 0 else
                    t >= answer and (t - answer) % return_period == 0)
                visiting = iterate(infos[x], t) == y
                assert scheduled == visiting
                actual_count += visiting
                formula_count = (0 if answer is None or t < answer else
                                 1 if return_period == 0 else 1 + (t - answer) // return_period)
                assert formula_count == actual_count
                counts["visit schedules and counts"] += 1
            pair, seen = (x, y), set()
            while pair not in seen and pair[0] != pair[1]:
                seen.add(pair)
                pair = f[pair[0]], f[pair[1]]
            coalesces = pair[0] == pair[1]
            assert coalesces == (iterate(infos[x], n) == iterate(infos[y], n))
            counts["synchronous coalescence pairs"] += 1
        # Exhaust every recognizable target set for the small exhaustive maps.
        if n <= 5:
            for mask in range(1 << n):
                g = tuple(v if mask >> v & 1 else f[v] for v in range(n))
                absorbing_info = orbit(g, x)
                output = iterate(absorbing_info, n)
                expected = next((v for v in infos[x][0] if mask >> v & 1), None)
                assert bool(mask >> output & 1) == (expected is not None)
                assert expected is None or output == expected
                if expected is not None:
                    assert absorbing_info[1] == infos[x][0].index(expected)
                    counts["first-target times"] += 1
                counts["absorbing-target outputs"] += 1
                cycle = infos[x][0][infos[x][1]:]
                recurring = bool(mask >> iterate(orbit(g, projected), n) & 1)
                reject = tuple(f[v] if mask >> v & 1 else v for v in range(n))
                eventually_always = bool(mask >> iterate(orbit(reject, projected), n) & 1)
                assert recurring == any(mask >> v & 1 for v in cycle)
                assert eventually_always == all(mask >> v & 1 for v in cycle)
                counts["recurring and permanent target predicates"] += 1


def main():
    counts = Counter()
    for n in range(1, 6):
        for f in product(range(n), repeat=n):
            check_map(f, counts)
    rng = Random(20261015)
    for n in (8, 16, 32):
        for _ in range(8):
            check_map(tuple(rng.randrange(n) for _ in range(n)), counts)
        check_map(tuple((i + 1) % n for i in range(n)), counts)
        check_map(tuple(min(i + 1, n - 1) for i in range(n)), counts)
        check_map(tuple(range(n)), counts)
    print("PASS: extension semantic checks succeeded.")
    print("Seed: 20261015")
    for name, count in sorted(counts.items()):
        print(f"{name}: {count:,}")
    print("Finite checks do not establish circuit size or historical novelty.")


if __name__ == "__main__":
    main()
