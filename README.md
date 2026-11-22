# Square-Root Circuit Bounds for Iterated Functions

Preliminary research draft, November 22, 2026.

How large a Boolean circuit is needed to evaluate an arbitrarily distant
iterate of a simple transition? For an n-bit map F of circuit size s, put
N = 2^n and E = min(N, sqrt(N(s+n²))). Every fixed power F^T has a circuit
of size O(E), independently of T. One circuit taking the starting state
and an m-bit exponent has size O(E + nm). A quadratic-size rank circuit
finds a checkpoint on an orbit. Shared half-word decoders charge each
row of its sparse lookup table only a constant number of gates.
For a linear-size transition and an n-bit exponent this gives O(n 2^(n/2)).
Lupanov's 2003 worst-case result over all maps has the sharp leading
term (1+o(1)) 2^n for an n-bit exponent.

The sorting construction gives additional bounds with A = s + n³ and
B = A + sqrt(n³ N A).

- **Graph navigation:** cycle labels, transient depth, pair-input reachability,
  exact first hitting times, and complete visit descriptors in O(B) gates.
- **Program analysis:** exact target-distance summaries, largest safe invariants,
  and termination ranks at the same square-root scale. A successor equation
  characterizes each summary, with a coNP-complete correctness check.
- **Batches:** r independent starting states with a common fixed exponent cost
  O(r A + sqrt(r n^3 N A)), for 1 <= r <= N.
- **Structured transitions:** r edits to a counter permutation give
  O(n(r+1)) gates for signed fixed powers and navigation, and O(n(r+m+1))
  for an m-bit input time. An autonomous q-bit controller with a p-bit affine
  payload gives O(2^q(q+p^2)) gates for each fixed power.

An explicit linear-size permutation has almost every power of complexity
Omega(2^(n/2)/n), for exponents uniform modulo its order. This matches the
upper bound's exponential scale. The counting argument identifies no explicit
hard exponent; hard exponents for this family have exponentially many binary digits.

Further extensions treat sharp constants and approximation, explicit exponent
complexity, a permutation near the counting ceiling, AKS sorting, depth and
width, reversible implementations, minimum checkpoint sets, and space-bounded
machines. The black-box lower bounds specify their algorithm restrictions;
the random-map results retain two unproved probabilistic hypotheses.

These are nonuniform bounded-fan-in Boolean circuits, with every lookup,
selection, and arithmetic gate charged. The general theorem bounds circuit
size. A separate construction analyzes preprocessing near the full state-space
scale. Under SETH, no general deterministic uniform analyzer or exact summary
compiler runs in 2^((1-epsilon)n) poly time for a fixed epsilon > 0, even on
instances whose requested power has a tiny circuit. The sparse
case additionally has a polynomial-time chart compiler from an explicit edit
list. Lean checks the core circuit bounds and selected extensions or semantic
components; the [Lean guide](lean/README.md) states each boundary. The new
certificate characterization and SETH reduction are prose proofs.

## Read and use

- [Paper (PDF)](iterated_function_circuits.pdf) and [LaTeX source](iterated_function_circuits.tex).
- [Lean guide](lean/README.md): public theorem map, exact gate bounds,
  dependencies, setup, and trusted boundary.
- [Review and validation record](REVIEW.md), [finite-check output](validation.txt),
  and [sparse-counter compiler](sparse_counter.py).
- [Submission metadata](submission_metadata.txt) and [bibliography](references.bib).

## Build and check

```sh
make             # Compile the paper; requires TeX Live or MiKTeX.
make check       # Run all finite semantic checks; requires Python 3.
make lean-check  # Build the formalization with its pinned Lean toolchain.
```

The LaTeX source embeds its bibliography and needs no external figures or
BibTeX run. The Lean guide covers dependency setup for a fresh checkout.
Finite checks exercise semantic identities; they do not prove gate bounds.

## Status and attribution

Lupanov's powering theorem also gives a sharp bound for self-maps of an
arbitrary M-point subset of the n-bit cube when M / log n tends to infinity.
It applies to every fixed finite complete Boolean basis. Igor Sergeev drew
our attention to the full proof. The earlier permutation result and an English
account of the general theorem are available online. [Lupanov (1993)](https://www.mathnet.ru/rus/vmumm2330), [Korshunov (2012), Theorem 2.3](https://doi.org/10.1070/RM2012v067n01ABEH004777).

The sorting construction extends Hirahara, Ilango, and Williams's
permutation-inversion argument to arbitrary fixed forward powers. The
resulting exponential-size inverter is compatible with polynomial-size
one-wayness. Priority for the size-dependent tradeoff remains open.
[Hirahara, Ilango, and Williams, §3.2](https://eccc.weizmann.ac.il/report/2023/171/).

Endpoint selection adapts Edgar’s closed-syncmer window rule to discrete
ranks with ties. Its density proof adapts the five-wise continuous-rank
argument presented by Knudsen and Stöckel.
[Edgar, Fig. 1](https://doi.org/10.7717/peerj.10805), [Knudsen and Stöckel, §5.1, Theorem 2](https://arxiv.org/abs/1502.05729).

The input-exponent construction uses Christian Reitwiessner's ancestry and
depth test for a transient target. Shared half-word tables and blocks of
cycle phases give the sharper fixed-power term in the resulting bound.
[Reitwiessner's input-time construction](https://github.com/SamuelSchlesinger/iterating-functions/pull/19).

The paper's related-work sections credit the underlying constructions, and its
provenance note credits Christian Reitwiessner's contributed extensions and
formalizations and describes AI assistance. Authorship and final attribution
remain provisional; no submission has been made. The review record identifies
the integrated PRs and the combined validation.
