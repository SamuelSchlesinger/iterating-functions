# Square-Root Circuit Bounds for Iterated Functions

Preliminary research draft, September 29, 2026.

## Files

- [LaTeX manuscript](iterated_function_circuits.tex): self-contained source.
- [PDF manuscript](iterated_function_circuits.pdf): compiled 13-page draft.
- [Bibliography](references.bib): matching entries for later editing; not required to compile.
- [Submission metadata](submission_metadata.txt): editable title, author field, keywords, and LaTeX abstract.
- [Semantic checks](verify_small_instances.py): finite checks using only the Python standard library.
- [Validation results](validation.txt): output of the checks in this package.
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
python3 verify_small_instances.py
```

## Mathematical scope

The manuscript proves the parameterized fixed-power circuit bound, its
optimized square-root consequence, an m-bit input-time version, a shared
batch construction, and a matching-exponent counting result for arbitrary
fixed powers of an explicit linear-size permutation. With N = 2^n and
A = s + n^3, the optimized bound is O(A + sqrt(n^3 N A)); for r trajectories
it is O(r A + sqrt(r n^3 N A)).

The circuit model is ordinary nonuniform bounded-fan-in Boolean circuits
with unrestricted fan-out. All dictionary access, sorting, selection, and
arithmetic gates are charged. The preprocessing needed to determine the
hardwired tables is not time-bounded. In the fixed-power theorem, the
circuit can depend on F and T but works for every starting state.

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
They are not a proof assistant formalization, an independently
synthesized gate-count verification, or evidence of historical novelty.

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
and separately entered title, abstract, authors, and keywords. Its current
homepage also warns that a submission with an essential AI-generated
component may be rejected regardless of merit. This package is not a claim
of submission eligibility or acceptance, and no submission has been made.

Official sources:
- https://eccc.weizmann.ac.il/static/colloquium/how_to_use/
- https://eccc.weizmann.ac.il/

## References consulted

The mathematical exposition cites Batcher's sorting networks, Hellman's
time-memory tradeoff, Munro--Raman--Raman--Rao's representations,
Hirahara--Ilango--Williams's inversion circuits, Eppstein's uniform iteration
classification, and Goldreich's one-way function definitions. Accessible
primary texts were consulted except for Batcher, whose reference uses the
original publication's bibliographic record. Section and theorem numbers
for Hirahara--Ilango--Williams refer to the ECCC full version.
