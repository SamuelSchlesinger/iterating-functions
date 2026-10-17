#!/usr/bin/env python3
"""Exhaustive finite checks for distance certificates and the SAT enumerator.

These checks validate semantic identities, not circuit-size bounds, coNP
completeness, or SETH. The distance oracle simulates until a target or repetition;
the certificate check only inspects a state and its successor.
"""

from itertools import product


def first_hit(f, target, x):
    seen = set()
    t = 0
    while x not in seen:
        if target >> x & 1:
            return t
        seen.add(x)
        x = f[x]
        t += 1
    return len(f)


def local_check(f, target, values):
    nstates = len(f)
    return all(
        0 <= values[x] <= nstates
        and values[x]
        == (0 if target >> x & 1 else min(nstates, values[f[x]] + 1))
        for x in range(nstates)
    )


def lifted_hit(f, target, x):
    if target >> x & 1:
        return 0
    power = tuple(x if target >> x & 1 else f[x] for x in range(len(f)))
    powers = []
    for _ in range(len(f).bit_length() - 1):
        powers.append(power)
        power = tuple(power[power[x]] for x in range(len(f)))
    r = 0
    for i in reversed(range(len(powers))):
        y = powers[i][x]
        if not (target >> y & 1):
            x = y
            r += 1 << i
    return r + 1


def check_distances():
    systems = candidates = queries = 0
    for nstates in (1, 2, 4):
        assignments = tuple(product(range(nstates + 1), repeat=nstates))
        for f in product(range(nstates), repeat=nstates):
            pair_distances = tuple(
                tuple(first_hit(f, 1 << y, x) for y in range(nstates))
                for x in range(nstates)
            )
            for x, y in product(range(nstates), repeat=2):
                expected = (
                    0 if x == y else min(nstates, 1 + pair_distances[f[x]][y])
                )
                assert pair_distances[x][y] == expected, (f, x, y)
            for target in range(1 << nstates):
                truth = tuple(first_hit(f, target, x) for x in range(nstates))
                systems += 1
                for values in assignments:
                    assert local_check(f, target, values) == (values == truth), (
                        f, target, values, truth
                    )
                    candidates += 1
                for x in range(nstates):
                    assert lifted_hit(f, target, x) == truth[x], (f, target, x)
                    invalid = list(truth)
                    invalid[x] = nstates + 1
                    assert not local_check(f, target, invalid)
                    queries += 1
    print(f"distance systems: {systems:,}")
    print(f"candidate certificates checked: {candidates:,}")
    print(f"binary-lifting and invalid-range checks: {queries:,} each")


def check_assignment_enumerator():
    queries = 0
    for m in (1, 2, 3):
        nassignments = 1 << m
        for truth_table in range(1 << nassignments):
            sat = int(truth_table != 0)
            for start, initial_flag in product(range(nassignments), range(2)):
                a, b = start, initial_flag
                for _ in range(nassignments):
                    b |= truth_table >> a & 1
                    a = (a + 1) % nassignments
                assert (a, b) == (start, initial_flag | sat)
                queries += 1
    print(f"assignment-enumerator queries: {queries:,}")


if __name__ == "__main__":
    check_distances()
    check_assignment_enumerator()
    print("PASS: program-summary semantic checks.")
