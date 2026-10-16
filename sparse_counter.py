"""Fast-forward permutations from a sparse list of edited counter successors.

Preprocessing and storage depend on the edit list, never on the universe size.
Python integers provide exact arithmetic. This is an executable semantic
compiler, not an extractor of the Boolean circuits proved in Lean.
"""
from bisect import bisect_left, bisect_right
from dataclasses import dataclass
from typing import Mapping


@dataclass(frozen=True)
class Arc:
    start: int
    length: int
    cycle: int
    position: int


@dataclass(frozen=True)
class TranslationTable:
    """Linear interval starts and offsets, with all additions modulo size."""

    size: int
    starts: tuple[int, ...]
    offsets: tuple[int, ...]

    def __call__(self, x: int) -> int:
        if not 0 <= x < self.size:
            raise ValueError("state outside the universe")
        i = bisect_right(self.starts, x) - 1
        return (x + self.offsets[i]) % self.size


class CounterChart:
    """Coordinates (cycle, position) for a sparsely edited circular counter.

    Each key of edits names an altered input and its value is the replacement
    successor. No-op edits are removed. Permutation preservation is checked by
    comparing edited outputs with the outputs freed by the edited inputs.
    Universes need not have power-of-two size.
    """

    def __init__(self, size: int, edits: Mapping[int, int]):
        if size < 1:
            raise ValueError("the universe must be nonempty")
        if any(not 0 <= x < size or not 0 <= y < size for x, y in edits.items()):
            raise ValueError("edited input or successor outside the universe")
        self.size = size
        self.edits = {x: y for x, y in edits.items() if y != (x + 1) % size}
        freed = {(x + 1) % size for x in self.edits}
        if len(set(self.edits.values())) != len(self.edits) or set(self.edits.values()) != freed:
            raise ValueError("edits do not preserve the permutation")
        self.cuts = tuple(sorted(self.edits))
        if not self.cuts:
            self.arcs = (Arc(0, size, 0, 0),)
            self.cycles = ((0,),)
            self.lengths = (size,)
            self.positions = ((0,),)
            return
        starts = tuple((self.cuts[i - 1] + 1) % size for i in range(len(self.cuts)))
        lengths = tuple((end - start) % size + 1 for start, end in zip(starts, self.cuts))
        start_index = {start: i for i, start in enumerate(starts)}
        successors = tuple(start_index[self.edits[end]] for end in self.cuts)
        arcs: list[Arc | None] = [None] * len(self.cuts)
        cycles, totals, positions = [], [], []
        for root in range(len(arcs)):
            if arcs[root] is not None:
                continue
            i, position, cycle = root, 0, []
            while arcs[i] is None:
                arcs[i] = Arc(starts[i], lengths[i], len(cycles), position)
                cycle.append(i)
                position += lengths[i]
                i = successors[i]
            assert i == root
            cycles.append(tuple(cycle))
            totals.append(position)
            positions.append(tuple(arcs[j].position for j in cycle))
        assert all(arc is not None for arc in arcs)
        self.arcs = tuple(arcs)
        self.cycles = tuple(cycles)
        self.lengths = tuple(totals)
        self.positions = tuple(positions)

    def encode(self, x: int) -> tuple[int, int]:
        if not 0 <= x < self.size:
            raise ValueError("state outside the universe")
        i = bisect_left(self.cuts, x) % len(self.cuts) if self.cuts else 0
        arc = self.arcs[i]
        return arc.cycle, arc.position + (x - arc.start) % self.size

    def decode(self, cycle: int, position: int) -> int:
        if not 0 <= cycle < len(self.cycles) or not 0 <= position < self.lengths[cycle]:
            raise ValueError("invalid cycle coordinate")
        j = bisect_right(self.positions[cycle], position) - 1
        arc = self.arcs[self.cycles[cycle][j]]
        return (arc.start + position - arc.position) % self.size

    def power(self, x: int, time: int) -> int:
        cycle, position = self.encode(x)
        return self.decode(cycle, (position + time) % self.lengths[cycle])

    def compile_power(self, time: int) -> TranslationTable:
        """Compile a signed power to at most 2*r+1 displacement intervals.

        Only E union H^{-1}(E) can contain a displacement-change edge.
        This discovers all changes using O(r) chart queries and a sort.
        Arithmetic also depends polynomially on the bit length of time.
        """
        candidates = set(self.edits)
        candidates.update(self.power(x, -time) for x in self.edits)
        starts = {0}
        for x in candidates:
            y = (x + 1) % self.size
            if (self.power(y, time) - y) % self.size != (self.power(x, time) - x) % self.size:
                starts.add(y)
        ordered = tuple(sorted(starts))
        return TranslationTable(
            self.size, ordered, tuple((self.power(x, time) - x) % self.size for x in ordered)
        )
