#!/usr/bin/env python3
"""Independent finite checks of sparse-counter charts and signed powers.

The exhaustive oracle traverses the full input permutation's cycles. The
compiler receives only edited successors. Huge-universe checks are explicitly
metamorphic; the exhaustive and sampled finite cases use the independent oracle.
"""
import argparse
import itertools
import json
import math
import random
from sparse_counter import CounterChart


def cycle_oracle(permutation):
    cycles, coordinates = [], {}
    for x in range(len(permutation)):
        if x in coordinates:
            continue
        cycle = []
        y = x
        while y not in coordinates:
            coordinates[y] = len(cycles), len(cycle)
            cycle.append(y)
            y = permutation[y]
        assert y == x
        cycles.append(cycle)

    def power(x, time):
        cycle, position = coordinates[x]
        values = cycles[cycle]
        return values[(position + time) % len(values)]

    return power, math.lcm(*(len(cycle) for cycle in cycles))


def check_permutation(permutation, times):
    size = len(permutation)
    edits = {x: y for x, y in enumerate(permutation) if y != (x + 1) % size}
    chart = CounterChart(size, edits)
    oracle, _ = cycle_oracle(permutation)
    for x in range(size):
        assert chart.decode(*chart.encode(x)) == x
        assert chart.power(x, 1) == permutation[x]
    for time in times:
        table = chart.compile_power(time)
        assert len(table.starts) <= 2 * len(edits) + 1
        expected = [oracle(x, time) for x in range(size)]
        defect = {x for x in range(size)
                  if expected[(x + 1) % size] != (expected[x] + 1) % size}
        assert defect <= set(edits) | {x for x in range(size) if expected[x] in edits}
        assert len(defect) <= 2 * len(edits)
        for x, y in enumerate(expected):
            assert chart.power(x, time) == y
            assert table(x) == y


def gf_mul(a, b, polynomial):
    value = 0
    width = polynomial.bit_length() - 1
    while b:
        if b & 1:
            value ^= a
        b >>= 1
        a <<= 1
        if a >> width:
            a ^= polynomial
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-size', type=int, default=8)
    args = parser.parse_args()
    rng = random.Random(20261016)
    counts = {'seed': 20261016, 'exhaustive_permutations': 0, 'distinct_powers': 0,
              'random_sparse_permutations': 0, 'binary_field_examples': 0,
              'huge_universe_metamorphic_examples': 0, 'rejected_invalid_lists': 0}
    for size in range(1, args.max_size + 1):
        for permutation in itertools.permutations(range(size)):
            _, order = cycle_oracle(permutation)
            check_permutation(permutation, range(order))
            counts['exhaustive_permutations'] += 1
            counts['distinct_powers'] += order
    for _ in range(1000):
        size = rng.randint(2, 512)
        cuts = rng.sample(range(size), rng.randint(0, min(32, size)))
        targets = [(x + 1) % size for x in cuts]
        rng.shuffle(targets)
        permutation = [(x + 1) % size for x in range(size)]
        for x, y in zip(cuts, targets):
            permutation[x] = y
        time = rng.getrandbits(rng.randint(1, 1024)) * rng.choice([-1, 1])
        check_permutation(permutation, (time, -time, 0))
        counts['random_sparse_permutations'] += 1
    # Binary polynomial bases; validate the primitive element by enumerating its powers.
    for width, polynomial in ((2, 0b111), (3, 0b1011), (4, 0b10011),
                              (5, 0b100101), (6, 0b1000011),
                              (7, 0b10000011), (8, 0x11d)):
        size = 1 << width
        powers, x = [], 1
        for _ in range(size - 1):
            powers.append(x)
            x = gf_mul(x, 2, polynomial)
        assert x == 1 and set(powers) == set(range(1, size))
        decode = [0] + powers
        encode = {x: i for i, x in enumerate(decode)}
        linear = [gf_mul(x, 2, polynomial) for x in range(size)]
        for _ in range(100):
            cuts = rng.sample(range(size), rng.randint(0, min(16, size)))
            targets = [linear[x] for x in cuts]
            rng.shuffle(targets)
            permutation = linear.copy()
            for x, y in zip(cuts, targets):
                permutation[x] = y
            conjugate = [encode[permutation[decode[i]]] for i in range(size)]
            r = sum(a != b for a, b in zip(permutation, linear))
            assert sum(y != (i + 1) % size for i, y in enumerate(conjugate)) <= r + 2
            check_permutation(conjugate, (-rng.getrandbits(256), 0, rng.getrandbits(256)))
            counts['binary_field_examples'] += 1
    for _ in range(100):
        # Impossible to enumerate: storage must remain proportional to the edits.
        size = 1 << rng.randint(64, 256)
        cuts = set(rng.randrange(size) for _ in range(32))
        targets = [(x + 1) % size for x in cuts]
        rng.shuffle(targets)
        chart = CounterChart(size, dict(zip(cuts, targets)))
        assert len(chart.arcs) <= max(1, len(cuts))
        time, other = rng.getrandbits(1024), -rng.getrandbits(1024)
        table = chart.compile_power(time)
        states = {0, size - 1, *(rng.randrange(size) for _ in range(30))}
        states.update((x + d) % size for x in cuts for d in (-1, 0, 1))
        for x in states:
            assert chart.decode(*chart.encode(x)) == x
            assert table(x) == chart.power(x, time)
            assert chart.power(chart.power(x, time), other) == chart.power(x, time + other)
        counts['huge_universe_metamorphic_examples'] += 1
    for size, edits in ((0, {}), (4, {0: 0}), (4, {0: 1, 1: 1}), (4, {-1: 0}), (4, {0: 4})):
        try:
            CounterChart(size, edits)
        except ValueError:
            counts['rejected_invalid_lists'] += 1
        else:
            raise AssertionError('invalid list accepted')
    print(json.dumps(counts, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
