#!/usr/bin/env python3
"""Finite checks for the queried-iterate construction.

These checks validate the selection rules of the proof on small functional
graphs. They do not check gate bounds; Lean does that.
"""

import random


def orbit(f, x, steps):
    states = [x]
    for _ in range(steps):
        states.append(f[states[-1]])
    return states


def random_map(rng, size, kind):
    if kind == 0:
        return [rng.randrange(size) for _ in range(size)]
    if kind == 1:
        order = list(range(size))
        rng.shuffle(order)
        f = [0] * size
        for i, x in enumerate(order):
            f[x] = order[(i + 1) % size]
        for _ in range(size // 6):
            f[rng.randrange(size)] = rng.randrange(size)
        return f
    f = [max(0, x - 1 - rng.randrange(3)) for x in range(size)]
    f[0] = rng.randrange(size)
    return f


def cyclic_states(f):
    states = set(range(len(f)))
    for _ in f:
        states = {f[x] for x in states}
    return states


def checkpoints(f, path_length):
    used, marks = set(), set()
    for x in range(len(f)):
        path = orbit(f, x, path_length - 1)
        if len(set(path)) == path_length and not used & set(path):
            used |= set(path)
            marks.add(path[-1])
    return marks


def forest(f, cyclic, depth, marks):
    """Return marked vertices with ancestry intervals in a preorder."""
    hull = set()
    for x in marks:
        while x not in cyclic:
            hull.add(x)
            x = f[x]
        hull.add(x)
    children = {x: [] for x in hull}
    for x in hull:
        if x not in cyclic:
            children[f[x]].append(x)
    roots = [x for x in hull if x in cyclic]
    marked = set(marks) | set(roots)
    marked |= {x for x in hull if len(children[x]) >= 2}
    assert len(marked) <= 2 * len(marks)
    low, high, rank = {}, {}, 0
    for root in roots:
        stack = [(root, 0)]
        while stack:
            x, i = stack.pop()
            if i == 0:
                low[x] = rank
                rank += 1
            if i < len(children[x]):
                stack.append((x, i + 1))
                stack.append((children[x][i], 0))
            else:
                high[x] = rank - 1
    return marked, low, high


def labels(f):
    result = []
    for x in range(len(f)):
        seen = {}
        states = []
        y = x
        while y not in seen:
            seen[y] = len(states)
            states.append(y)
            y = f[y]
        entry = seen[y]
        cycle = states[entry:]
        canonical = min(cycle)
        position = entry + cycle.index(canonical)
        result.append((entry, len(cycle), canonical, -position % len(cycle)))
    return result


def walk(f, base, steps, limit):
    assert 0 <= steps <= limit
    return orbit(f, base, steps)[-1]


def query(f, data, limit, x, u):
    marks, marked, low, high, label = data
    depth, length, canonical, phase = label[x]
    if u < depth:
        if u <= limit:
            return walk(f, x, u, limit)
        hit = next(y for y in orbit(f, x, limit) if y in marks)
        target_depth = depth - u
        eligible = [
            a
            for a in marked
            if low[a] <= low[hit] <= high[a]
            and target_depth <= label[a][0] <= target_depth + limit
        ]
        assert eligible
        return [
            walk(f, a, label[a][0] - target_depth, limit) for a in eligible
        ]
    position = (phase + u) % length
    if position <= limit:
        return walk(f, canonical, position, limit)
    eligible = [
        a
        for a in marks
        if label[a][0] == 0
        and label[a][2] == canonical
        and label[a][3] <= position <= label[a][3] + limit
    ]
    assert eligible
    return [walk(f, a, position - label[a][3], limit) for a in eligible]


def main():
    rng = random.Random(20261030)
    maps = queries = selected = 0
    for trial in range(360):
        size = rng.choice([8, 16, 24, 32, 48, 64])
        f = random_map(rng, size, trial % 3)
        cyclic = cyclic_states(f)
        label = labels(f)
        depth = [entry[0] for entry in label]
        for path_length in (1, 2, 3, 5, 8):
            marks = checkpoints(f, path_length)
            marked, low, high = forest(f, cyclic, depth, marks)
            data = (marks, marked, low, high, label)
            limit = 2 * path_length
            maps += 1
            for x in range(size):
                states = orbit(f, x, 2 * size)
                for u in range(2 * size):
                    answer = query(f, data, limit, x, u)
                    answers = answer if isinstance(answer, list) else [answer]
                    assert all(value == states[u] for value in answers)
                    queries += 1
                    selected += len(answers)
    print(f"Queried iterates: {maps} map/spacing pairs, {queries} queries, "
          f"{selected} selected marks agree with direct simulation.")


if __name__ == "__main__":
    main()
