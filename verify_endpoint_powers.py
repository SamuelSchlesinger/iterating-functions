#!/usr/bin/env python3
"""Check endpoint selection and both recovery circuits against explicit orbits."""

from collections import Counter
from itertools import product


class Graph:
    def __init__(self, successor):
        self.successor = successor
        self.states = range(len(successor))
        self.paths = []
        self.depth = []
        self.origin = []
        self.phase = []
        self.cycles = {}
        for start in self.states:
            path = []
            state = start
            while state not in path:
                path.append(state)
                state = successor[state]
            depth = path.index(state)
            cycle = path[depth:]
            origin = min(cycle)
            index = cycle.index(origin)
            self.cycles[origin] = cycle[index:] + cycle[:index]
            self.paths.append(path)
            self.depth.append(depth)
            self.origin.append(origin)
            self.phase.append((-index - depth) % len(cycle))

        children = [[] for _ in self.states]
        for x in self.states:
            if self.depth[x]:
                children[successor[x]].append(x)
        self.pre = [0] * len(successor)
        self.high = [0] * len(successor)
        order = []

        def visit(x):
            self.pre[x] = len(order)
            order.append(x)
            for child in children[x]:
                visit(child)
            self.high[x] = len(order) - 1

        for root in self.states:
            if not self.depth[root]:
                visit(root)
        assert len(order) == len(successor)

    def power(self, x, t):
        path = self.paths[x]
        if t < len(path):
            return path[t]
        depth = self.depth[x]
        return path[depth + (t - depth) % (len(path) - depth)]

    def walk(self, x, steps):
        for _ in range(steps):
            x = self.successor[x]
        return x


def weak_orders(size):
    """Every order with ties, once up to order-preserving relabeling."""
    for ranks in product(range(size), repeat=size):
        if set(ranks) == set(range(1 + max(ranks))):
            yield ranks


def check(graph, ranks, length, counts):
    k = 2 * length
    marks = []
    for h in graph.states:
        window = [graph.power(h, i) for i in range(length + 1)]
        if len(set(window)) == len(window):
            least = min(ranks[v] for v in window)
            if least in (ranks[window[0]], ranks[window[-1]]):
                marks.append(h)

    block = 1 << (length.bit_length() - 1)
    blocks = {}
    for origin in {graph.origin[h] for h in marks}:
        cycle = graph.cycles[origin]
        for i in range(0, len(cycle), block):
            blocks[origin, i // block] = cycle[i]
    assert len(blocks) <= len(marks) + len(graph.states) // block

    for x in graph.states:
        trace = [graph.power(x, i) for i in range(2 * k + 1)]
        prefix = trace[:k]
        least = min(ranks[y] for y in prefix)
        minima = [i for i, y in enumerate(prefix) if ranks[y] == least]
        positions = {i if i < length else i - length for i in minima}
        periods = [p for p in range(1, k + 1) if trace[k + p] == trace[k]]
        if len(set(prefix)) == k:
            assert all(trace[d] in marks for d in positions)
        else:
            assert periods

        # Last minimum matches the priority scan in the fixed-power circuit.
        i = minima[-1]
        d = i if i < length else i - length
        h = trace[d]
        times = (*range(2 * k + len(graph.states) + 1), (1 << 65) + 3)
        for t in times:
            expected = graph.power(x, t)
            if t < k:
                assert trace[t] == expected
                counts["short prefix"] += 1
                continue
            if periods:
                # Every flagged return gives the correct fixed-time wire.
                for p in periods:
                    assert trace[k + (t - k) % p] == expected
                counts["short return"] += 1
                continue

            assert h in marks
            payload = graph.power(h, t - k)
            assert graph.walk(payload, k - d) == expected
            u = t - d
            if u < graph.depth[h]:
                target = graph.depth[h] - u
                rows = [a for a in marks
                        if graph.pre[a] <= graph.pre[h] <= graph.high[a]
                        and target <= graph.depth[a] <= target + k]
                if u >= k:
                    assert rows
                    counts["long transient"] += 1
                for a in rows or [h]:
                    steps = graph.depth[a] - target
                    assert 0 <= steps <= k
                    assert graph.walk(a, steps) == expected
                counts["transient"] += 1
            else:
                origin = graph.origin[h]
                phase = (graph.phase[h] + u) % len(graph.cycles[origin])
                j, steps = divmod(phase, block)
                assert graph.walk(blocks[origin, j], steps) == expected
                counts["cycle"] += 1
                if j and steps:
                    counts["interior of later cycle block"] += 1


def main():
    counts = Counter()
    ranks = list(weak_orders(4))
    assert len(ranks) == 75
    for successor in product(range(4), repeat=4):
        graph = Graph(successor)
        for order in ranks:
            for length in range(1, 5):
                check(graph, order, length, counts)
    print("All 256 two-bit maps, 75 weak rank orders, four window lengths, and every start passed.")
    # The full two-bit space cannot realize every long transient or block offset.
    for successor in ((1, 2, 3, 4, 5, 6, 7, 7), (1, 2, 3, 4, 5, 6, 7, 0)):
        graph = Graph(successor)
        for order in (tuple(range(8)), (0,) * 8, tuple(reversed(range(8)))):
            for length in (1, 2, 3, 4):
                check(graph, order, length, counts)
    for kind in ("short prefix", "short return", "long transient", "transient",
                 "cycle", "interior of later cycle block"):
        assert counts[kind] > 0
    print("Eight-state boundary cases passed, including a long transient and later cycle blocks.")


if __name__ == "__main__":
    main()
