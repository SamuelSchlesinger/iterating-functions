#!/usr/bin/env python3
"""Finite semantic checks for the iterated-function circuit construction.

This tests the graph lemma, shifted-payload identity, residue-table branch,
and a sorting-network realization of batch lookup, plus the inverse-power
identity for permutations.  It is not a formal
verification of a synthesized Boolean circuit or of its asymptotic size.
Only Python's standard library is required.
"""
from __future__ import annotations

import argparse
import itertools
import math
import random
from collections import Counter
from typing import Sequence


def orbit(f: Sequence[int], x: int) -> tuple[list[int], int]:
    """Return distinct orbit states and the index of the first cycle state."""
    seen: dict[int, int] = {}
    path: list[int] = []
    while x not in seen:
        seen[x] = len(path)
        path.append(x)
        x = f[x]
    return path, seen[x]


def power(f: Sequence[int], x: int, t: int) -> int:
    if t < 0:
        raise ValueError("negative iterate")
    path, mu = orbit(f, x)
    if t < len(path):
        return path[t]
    return path[mu + (t - mu) % (len(path) - mu)]


def graph_data(f: Sequence[int]) -> tuple[list[int], set[tuple[int, ...]]]:
    depths: list[int] = []
    cycles: set[tuple[int, ...]] = set()
    for x in range(len(f)):
        path, mu = orbit(f, x)
        depths.append(mu)
        cycle = path[mu:]
        start = cycle.index(min(cycle))
        cycles.add(tuple(cycle[start:] + cycle[:start]))
    return depths, cycles


def checkpoints(
    depths: Sequence[int], cycles: set[tuple[int, ...]], length: int
) -> set[int]:
    counts = [0] * length
    for depth in depths:
        if depth:
            counts[depth % length] += 1
    residue = min(range(length), key=lambda r: counts[r])
    h = {x for x, d in enumerate(depths) if d and d % length == residue}
    for cycle in cycles:
        if len(cycle) >= length:
            h.update(cycle[::length])
    assert len(h) * length <= 2 * len(depths)
    return h


def checked_shortcut(
    f: Sequence[int], h: set[int], length: int, x: int, t: int
) -> tuple[int, str]:
    k = 2 * length
    if t < k:
        state = x
        for _ in range(t):
            state = f[state]
        return state, "short-time"
    prefix = [x]
    for _ in range(k):
        prefix.append(f[prefix[-1]])
    hits = [(i, y) for i, y in enumerate(prefix) if y in h]
    if hits:
        d, checkpoint = hits[0]
        payload = power(f, checkpoint, t - k)
        result = payload
        for _ in range(k - d):
            result = f[result]
        return result, "checkpoint"
    # Select an adjacent equal-state pair in state/index sorted order,
    # exactly as in the repeated-state circuit primitive.
    records = sorted((y, i) for i, y in enumerate(prefix))
    pairs = [
        (left[1], right[1])
        for left, right in zip(records, records[1:])
        if left[0] == right[0]
    ]
    assert pairs, (f, length, x, "checkpoint lemma failed")
    i, j = pairs[0]
    assert i < j
    period = j - i
    table_value = t % period
    offset = (table_value - (i % period)) % period
    index = i + offset
    assert i <= index < j <= k
    return prefix[index], "repetition"


def bitonic_sort(records: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    """Compare-and-swap sorting network; length must be a power of two."""
    a = records.copy()
    n = len(a)
    assert n >= 1 and n & (n - 1) == 0
    size = 2
    while size <= n:
        distance = size // 2
        while distance:
            for i in range(n):
                j = i ^ distance
                if j > i:
                    ascending = (i & size) == 0
                    if (a[i] > a[j]) == ascending:
                        a[i], a[j] = a[j], a[i]
            distance //= 2
        size *= 2
    return a


def batch_lookup(dictionary: dict[int, int], queries: list[int]) -> list[tuple[bool, int]]:
    # (dummy, key, dictionary/query tag, original index, payload)
    records = [(0, key, 0, i, value)
               for i, (key, value) in enumerate(dictionary.items())]
    records.extend((0, key, 1, i, 0) for i, key in enumerate(queries))
    width = 1 << max(0, (len(records) - 1).bit_length())
    records += [(1, 0, 0, i, 0) for i in range(width - len(records))]
    records = bitonic_sort(records)
    found = False
    payload = 0
    previous_key: int | None = None
    restored: list[tuple[int, ...]] = []
    for dummy, key, tag, index, value in records:
        if dummy:
            restored.append((1, 0, 0, 0))
            continue
        if key != previous_key:
            found = False
            payload = 0
        if tag == 0:
            found = True
            payload = value
            restored.append((1, 0, 0, 0))
        else:
            restored.append((0, index, int(found), payload if found else 0))
        previous_key = key
    restored = bitonic_sort(restored)
    return [(bool(row[2]), row[3]) for row in restored[:len(queries)]]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260929)
    parser.add_argument("--random-graphs", type=int, default=40,
                        help="number of random maps at each larger state size")
    args = parser.parse_args()
    rng = random.Random(args.seed)
    counts: Counter[str] = Counter()

    def check_map(f: Sequence[int], exhaustive: bool) -> None:
        size = len(f)
        depths, cycles = graph_data(f)
        lengths = (range(1, size + 1) if exhaustive else
                   sorted({1, 2, 3, max(1, math.isqrt(size)), max(1, size // 2), size}))
        starts = list(range(size)) if exhaustive or size <= 16 else rng.sample(range(size), 16)
        for length in lengths:
            h = checkpoints(depths, cycles, length)
            k = 2 * length
            times = sorted({0, 1, max(0, k - 1), k, k + 1, 3 * size + 7,
                            (1 << 257) + 20260929})
            for x in starts:
                # Check the graph lemma independently of the selected exponent.
                prefix = [x]
                for _ in range(k):
                    prefix.append(f[prefix[-1]])
                assert any(y in h for y in prefix) or len(set(prefix)) < len(prefix)
                counts["checkpoint-lemma instances"] += 1
                for t in times:
                    actual, branch = checked_shortcut(f, h, length, x, t)
                    expected = power(f, x, t)
                    assert actual == expected, (f, length, x, t, actual, expected)
                    counts[f"outputs: {branch}"] += 1
        counts["maps"] += 1

    for size in range(1, 5):
        for f in itertools.product(range(size), repeat=size):
            check_map(f, exhaustive=True)
    for size in (8, 16, 32, 64):
        for _ in range(args.random_graphs):
            check_map([rng.randrange(size) for _ in range(size)], exhaustive=False)

    # Exercise zero payloads, empty dictionaries, duplicate queries, and padding.
    for _ in range(2000):
        keys = rng.sample(range(32), rng.randrange(17))
        dictionary = {key: rng.randrange(256) for key in keys}
        queries = [rng.randrange(32) for _ in range(rng.randrange(1, 33))]
        actual = batch_lookup(dictionary, queries)
        expected = [(key in dictionary, dictionary.get(key, 0)) for key in queries]
        assert actual == expected, (dictionary, queries, actual, expected)
        counts["batch-lookup instances"] += 1

    for b in range(1, 129):
        d = math.lcm(*range(1, b + 1))
        assert d * (b + 1) >= (1 << b)
        for j in range(b + 1):
            assert d % math.comb(b, j) == 0
        counts["lcm lemma instances"] += 1

    for k in range(1, 6):
        bmax = (1 << k) - 1
        width = 1 << k
        f = []
        for a in range(width):
            for b in range(width):
                new_b = (b + 1) % a if 1 <= a and b < a else b
                f.append(a * width + new_b)
        assert sorted(f) == list(range(len(f)))
        for a in range(width):
            for b in range(width):
                old_b = (b - 1 if b else a - 1) if 1 <= a and b < a else b
                assert f[a * width + old_b] == a * width + b
                counts["explicit inverse states"] += 1
        _, cycles = graph_data(f)
        assert math.lcm(*(len(c) for c in cycles)) == math.lcm(*range(1, bmax + 1))
        counts["permutation family instances"] += 1

    # Check P^(ord(P)-1) against the inverse table, including long exponents
    # congruent to -1 modulo the order, for every small permutation and L.
    for size in range(1, 6):
        for f in itertools.permutations(range(size)):
            depths, cycles = graph_data(f)
            order = math.lcm(*(len(c) for c in cycles))
            inverse = [0] * size
            for x, y in enumerate(f):
                inverse[y] = x
            for length in range(1, size + 1):
                h = checkpoints(depths, cycles, length)
                for t in (order - 1, order * (1 << 257) - 1):
                    for y in range(size):
                        actual, _ = checked_shortcut(f, h, length, y, t)
                        assert actual == inverse[y], (f, length, t, y, actual)
                        counts["inverse-power instances"] += 1

    print("PASS: all finite semantic checks succeeded.")
    print(f"Seed: {args.seed}")
    for key in sorted(counts):
        print(f"{key}: {counts[key]:,}")
    print("These checks do not replace a proof or establish historical novelty.")


if __name__ == "__main__":
    main()
