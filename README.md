# Square-Root Circuit Bounds for Iterated Functions

Preliminary research draft, October 16, 2026.

## Files

- [LaTeX manuscript](iterated_function_circuits.tex): self-contained source, introductory results table, and quantitative Lean appendix.
- [PDF manuscript](iterated_function_circuits.pdf): compiled draft.
- [Bibliography](references.bib): matching entries for later editing; not required to compile.
- [Submission metadata](submission_metadata.txt): editable title, author field, keywords, and LaTeX abstract.
- [Semantic checks](verify_small_instances.py): finite checks using only the Python standard library.
- [Validation results](validation.txt): output of the checks in this package.
- [Lean formalization](lean/README.md): checked circuit constructions, navigation, and the lower bound.
- [Detailed review](REVIEW.md): all ten proposals, proof requirements, and attribution.
- [Extension checks](verify_extensions.py): graph labels, hitting times, and checkpoint refinements.
- [Sparse-counter compiler](sparse_counter.py): arc coordinates and signed-power interval tables.
- [Sparse-counter checks](verify_sparse_counter.py): exhaustive and sampled independent cycle oracles.
- [Makefile](Makefile): compilation and checking commands.

## Build

A standard TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. No external figures, font files, or BibTeX run are
needed. The bibliography is embedded in the main source.

Run `make`, or run the following command three times so that all labels and
PDF bookmarks stabilize:

```sh
pdflatex -interaction=nonstopmode -halt-on-error iterated_function_circuits.tex
```

To run the semantic checks:

```sh
make check
```

To check the formalization, with the pinned Lean toolchain installed:

```sh
make lean-check
```

See [lean/README.md](lean/README.md) for fresh-checkout setup, exact dependency
revisions, the public statements, and the axiom audit.

## Mathematical scope

The manuscript proves the parameterized fixed-power circuit bound, its
optimized square-root consequence, an m-bit input-time version, a shared
batch construction, and a matching-exponent counting result for arbitrary
fixed powers of an explicit linear-size permutation. With N = 2^n and
A = s + n^3, the optimized bound is O(A + sqrt(n^3 N A)); for r trajectories
it is O(r A + sqrt(r n^3 N A)).
The fixed-power tradeoff also replaces N by Q_L, the number of deep transient
states and long-cycle vertices at scale L. This refinement is checked in Lean.
Writing B = A + sqrt(n^3 N A), arbitrarily wide m-bit input times cost
O(min(m B, n B + n m)); this improved bound is also checked in Lean.
For the explicit lower-bound permutation, almost every power is hard when
the exponent is uniform modulo the full period. Lean also checks the
equivalence with fixed-integer remainder circuits and an exponential lower
bound on the description length of hard exponents.

The circuit model is ordinary nonuniform bounded-fan-in Boolean circuits
with unrestricted fan-out. All dictionary access, sorting, selection, and
arithmetic gates are charged. The circuit theorem does not charge the
preprocessing needed to determine the hardwired tables. In the fixed-power
theorem, the circuit can depend on F and T but works for every starting state.

For a permutation differing from the ordinary counter at r states, the paper
proves O(n(r+1)) gates for every signed fixed power and O(n(r+m+1)) for an
m-bit input time. Its arc chart is compiled from the edit list without
state-space enumeration. Both coordinate directions are charged when this is
transported to other cycles. A binary-field application uses Kleinjung and
Wesolowski's fixed-characteristic discrete-logarithm theorem. The classical
commutation/block geometry is credited to Moreno and Rivera.

Lean checks the sparse fixed-power, centralizer, and additive input-time
bounds, with both coordinate costs charged. The interval encoder also gives
cycle labels in O(n(r+1)) gates. The chart existence proof and all Boolean
gate costs are checked; the Python edit-list compiler's algorithm and runtime,
and the finite-field application, remain outside the Lean boundary.

The counting result does not identify an explicit hard exponent. Every
exponent witnessing the stated lower bound necessarily has binary length
Omega(2^(n/2)/n^2). For that particular permutation the bounded-bit-time
iterator is easy, as is the update permutation's inverse.

The new inversion corollary uses P^(-1) = P^(ord(P)-1). It yields exact
inversion circuits of size 2^(n/2) times a polynomial for polynomial-size
permutations. This exponential upper bound is compatible with one-wayness
against polynomial-size circuits and does not settle the existence of
one-way functions. The section distinguishes permutation inversion from
inversion of general functions and worst-case evaluation hardness from
average-case inversion hardness.

The finite checks exercise the combinatorial construction and its
arithmetic identities, including 258-bit exponents and repeated-state
cases, plus exact inversion on every permutation of at most five states.
These finite tests do not establish gate counts or historical novelty.
Separately, the Lean development checks actual Boolean circuit constructions,
semantics, and size for the fixed-power tradeoff and its invariant-set,
image-sensitive, and encoded-state forms, real square-root optimization,
permutation inversion, variable-time and batched evaluation, cycle labels,
transient depth, reachability and first hitting times, recognizable targets,
and halting complete configurations. It also checks the matching-exponent
lower bound, including the linear-size update circuit. See the theorem map
in `lean/README.md` for precise statements and explicit constants.

An autonomous q-bit controller acting on a p-bit affine payload has
O(2^q(q+p^2)) gates for every fixed power, and m times this bound for an
m-bit input time. Both statements are now checked in Lean, together with
a polynomial specialization for polynomially many controller states.
The result allows singular and noncommuting affine maps. A generic checked
theorem replaces affine maps by any composition-closed family whose every
member has a uniformly bounded evaluation circuit.

The paper and Lean also include O(B)-gate eventual synchronous coalescence
and recurring/permanent recognizable-target queries.
Complete visit schedules use O(n B) gates: a success flag, first visit time,
and return period describe all visits. Lean checks the exact counting formula
through any deadline as an arithmetic interpretation of that descriptor.

The paper now includes O(B)-gate transient depth and an O(n B)-gate pair-input
reachability/first-hitting-time theorem. The review records the other proposals
and their qualifications. The checkpoint proof uses disjoint path packing,
giving at most floor(|S|/L) checkpoints on an invariant set S, including
finite subsets of state types in arbitrary universes.

## Before submission

The exact historical priority of the full fixed-power theorem has not been
established. The draft explicitly generalizes the permutation-inversion
construction in Section 3.2 of Hirahara, Ilango, and Williams, rather than
their broader general-function inversion and compression results.
Checkpointing, sorting-based lookup, and square-root-size permutation
inversion are credited to prior work. Expert review of the precise novelty
claim is still needed.

The author field is provisionally set to Samuel Schlesinger. No affiliation
or email address is invented. Confirm the authorship and retain an accurate
account of assistance and attribution when preparing a submission.

The draft includes a provenance note covering AI assistance in statement
development, proof development, writing, and literature search.

ECCC's official instructions, checked September 29, 2026, require a PDF
and separately entered title, abstract, authors, and keywords. At that check,
its homepage also warned that a submission with an essential AI-generated
component may be rejected regardless of merit. This package is not a claim
of submission eligibility or acceptance, and no submission has been made.

Official sources:
- https://eccc.weizmann.ac.il/static/colloquium/how_to_use/
- https://eccc.weizmann.ac.il/

## References consulted

The mathematical exposition cites Batcher's sorting networks, Hellman's
time-memory tradeoff, Munro--Raman--Raman--Rao's representations,
Hirahara--Ilango--Williams's inversion circuits, Eppstein's uniform iteration
classification, Gagie--He--Navarro's path queries, and Goldreich's one-way
function definitions. The formalization additionally credits Mathlib, CSLib,
and the author's Circuit library in Complexitylib. Accessible
primary texts were consulted except for Batcher, whose reference uses the
original publication's bibliographic record. Section and theorem numbers
for Hirahara--Ilango--Williams refer to the ECCC full version.
