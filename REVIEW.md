# Detailed review and formalization record

Reviewed against local baseline `2a0bb654c27fc7650c901b946c7a2bba36212536` and
the ten proposed additions. Revision date: October 16, 2026.

The fixed-power argument survives the review. The new Lean development proves
its parameterized gate bound end to end, so the main correctness conclusion
now has more than finite experimental support. All ten proposals have valid
mathematical routes, with the qualifications below. This is not a claim that
all ten are novel or mechanized.

The revision incorporates cycle labels, reachability and hitting times, image
sensitivity, recognizable targets, complete-configuration simulation, and the
formalization account. Lean now checks the fixed-power tradeoff and real
optimization, invariant sets and encodings, permutation inversion, variable-time
and shared batched evaluation, targets and halting computations, exact cycle
labels and navigation, and the matching-exponent lower bound. The other
proposals remain distinct from this checked boundary; `lean/README.md` maps
public statements to their precise contracts.

## Findings that affect the statements

- **Earliest repetition matters for exact cycle length.** An arbitrary repeated
  pair gives a period, possibly a multiple of the least period. To recover the
  exact cycle, minimize the second occurrence index among adjacent duplicates
  after sorting by state and original index. The earliest repeated prefix has
  no earlier duplicates, so its repeat interval traverses the cycle exactly once.
- **State length and cycle length have different endpoint requirements.** A cycle
  may have length `2^n`; its length field needs `n+1` bits. First hitting times
  are at most `2^n-1`, so a separate reachability bit and `n` time bits suffice.
- **A phase is an eventual label.** For transient `x`, the equality with the
  canonical cycle orbit starts at `t = mu(x)`. It need not hold at `t = 0`.
- **Nonuniformity is essential.** Huge exponents enter hardwired payloads and
  bounded residue tables. Neither the formalization nor the asymptotic theorem
  supplies an efficient algorithm for discovering these tables from succinct `F`.
- **Circuit costs must be Boolean costs.** Universe polymorphism does not
  justify a primitive that computes an arbitrary state transformation in one
  gate. The encoded-state theorem preserves bit width and charges the supplied
  transition circuit, sorting, lookup, arithmetic, and selection.
- **Historical priority remains unresolved.** The closest identified circuit
  construction already has the checkpoint, shared lookup, and forward-correction
  ingredients for permutation inversion. Navigation itself is also established
  in other representation models. The paper must identify its precise total-gate
  claim without describing all these ingredients as new.

## Audit of the original manuscript

The fixed-power correction is forward-only and does not use cancellation or
an inverse of `F`: from `h=F^d(x)`, it evaluates
`F^(K-d)(F^(T-K)(h))=F^T(x)`, with `d≤K≤T`. The separate short-time branch
is necessary to keep those exponents nonnegative. For a repeated pair, a
period need not be minimal to justify reconstruction. Fixed bounded residue
tables avoid charging the length of `T` to an online arithmetic operation.
These points are checked in the formal development.

The original multiquery dictionary proof correctly sorts by key/tag/index,
propagates dictionary payloads across equal-key runs, and sorts back by query
position. A RAM lookup is not free in this argument. Original indices and
padding tags contribute to record width. In the batched theorem the assumption
`r≤N` keeps `log(rL+N/L)=O(n)`, which is needed for the displayed polynomial
factor. The batched result is a shared-construction upper bound, not a lower
bound separating optimal joint and separate circuits.

The variable-time proof uses separately constructed powers `F^(2^j)` on the
current state. It must apply the fixed-power theorem to `F` each time; recursively
feeding the previously enlarged circuit size into the upper bound would give a
different estimate. The paper's direct construction has the claimed `m` factor.

The lower bound counts distinct powers of an explicit low-complexity
permutation against the number of bounded-size circuits. It establishes
existence of hard fixed powers and the matching exponential scale, not an
explicit hard exponent or a hard iterator with a short time input. Restriction
to one output loses a factor of `n`, as stated. Its permutation also has an
easy inverse, so it is not a one-way-function construction.

The permutation-inversion corollary correctly uses an exponent representing
the inverse in the finite cyclic group. Its exponential circuit size is
compatible with security against polynomial-size circuits. For a general
noninjective map an inverse need not be a forward iterate; persisting a target
while searching for a preimage enlarges the full state. The original manuscript
explicitly records both limitations. No fatal correctness defect was found in
these arguments. The circuit constructions and matching-exponent lower bound
now have kernel-checked proofs; the short-exponent corollary and cryptographic
interpretations remain prose arguments.

## 1. Cycle labels: integrated and mechanized

Checkpoint metadata `(ell,c,phi)` occupies `O(n)` bits per record, provided the
cycle-length field has `n+1` bits. If `F^d(x)=h`, the proposed relation
`phi(x)=phi(h)-d mod ell(h)` follows by comparing sufficiently late iterates.
It remains valid when the hit occurs before either orbit has reached its cycle.

For the repetition branch, sort `(state,index)` records, inspect adjacent
equal-state pairs, and select the one with minimum second index `j`. If its
first index is `i`, then `i=mu`, `ell=j-i`, and the minimum state in `[i,j)` is
`x_p` for a unique `p`. The correct phase is `-p mod ell`, not `i-p mod ell`.
An interval mask and a minimum scan cost `O(nL)`; arithmetic costs `O(n^2)`.
The original sorting bound absorbs these costs. This proves `O(B)`.

This result labels the eventual orbit of each input. It does not output an
explicit description of every vertex and edge of the whole graph at once.
The paper uses “Computing the Structure of Functional Graphs” with that
per-input output contract stated explicitly.

The checked circuit uses a different route: apply `F^(N!)`, which preserves
cycle labels and phase, and then use a short cyclic scan or checkpoint lookup.
It proves the same `O(B)` bound, including modular arithmetic costs. The
semantic phase identities also hold for arbitrary finite types with an order.

## 2. Reachability and hitting times: integrated and mechanized

For `D=lcm(1,...,N)`, the test `F^D(z)=z` is exactly cyclicity. One direction
uses divisibility by the cycle length; the other only needs `D>0`, since any
positive return makes `z` periodic. There is no need to compare a huge `D`
inside the online circuit.

Search the inclusive interval `[0,N-1]`. The predicate is monotone, and its
right endpoint is true even for a chain of maximal transient length `N-1`.
Unroll at most `n` binary-search rounds. Each round has an `n`-bit variable-time
iteration circuit of size `O(nB)` followed by an `O(B)` cyclicity test. Thus
`O(n^2B)` is justified, including both endpoints and the adaptive dependence
between successive rounds.

For transient `y`, depth decreases by one along each noncyclic step. Therefore
the only possible hitting time is `mu(x)-mu(y)`; check nonnegativity and then
evaluate that iterate. Equal cycle labels alone would be insufficient because
different branches can feed the same cycle.

For cyclic `y`, equal canonical cycle representatives are necessary and
sufficient. The stated time
`mu(x) + ((phi(y)-phi(x)-mu(x)) mod ell(x))` is correct. Its value is at most
`mu(x)+ell(x)-1 ≤ N-1`. Return an explicit false flag on negative instances,
with an unspecified time field; an optional linear-size mask can return zero.
Both cases include `x=y`, whose answer is time zero. Lean checks the threshold
search, both cases, the decoded first-hitting-time specification, and the
`O(n^2 B)` gate bound. It uses `n+3` bits internally and `n+1` output time bits,
and proves the time is less than `N` on positive instances.

A further mathematical improvement is possible for the depth subproblem:
let `R=F^D`, and compare `F^i(x)` with `F^i(R(x))` through `2L` steps. Equality
holds exactly when the former state is cyclic, because `R` fixes cyclic states
and commutes with `F`. An equality gives the first cycle-entry position. If
there is no equality, a prefix repetition is impossible, so a checkpoint is
hit while still transient. Storing `mu(h)` then gives `mu(x)=d+mu(h)`.
This yields depth in `O(B)` and, with the existing variable-time iterator,
reachability in `O(nB)`. This sharper route is recorded for further development;
the integrated theorem retains the directly reviewed `O(n^2B)` proof.

## 3. Image sensitivity: valid, integrated, and mechanized

`F(image(F^d)) ⊆ image(F^d)` follows from commutation of iterates. Apply the
invariant-set fixed-power theorem after computing the burn-in. State words
remain `n` bits, while the checkpoint count uses `M_d`. A globally computable
membership test for the image is unnecessary: correctness is restricted to
the image, and the outer burn-in guarantees that its outputs enter that set.

The optimized claim assumes a nonempty state space, so `M_d≥1`. It includes
`T=d`, where the tail can be the identity. Lean proves the slightly stronger
tradeoff for all `1≤L≤2^n`, with natural-number division and harmless `+1`s.
The general real square-root optimization and invariant-set optimum are now checked. The exponential improvement
requires the stated cheap burn-in; a small image alone does not bound the cost
of computing the state that enters it.

## 4. Active long-trajectory mass: valid, not mechanized

Let the deep vertices have depth at least `L`. Choose one least-populated
depth residue modulo `L` among these vertices only. A trajectory starting
at depth at least `2L` sees every residue while it remains deep, so it hits
a mark in fewer than `L` steps. A shallower trajectory reaches its cycle in
fewer than `2L` steps. A long cycle then hits a cycle mark within another `L`
steps; a short cycle repeats within another `L` steps.

Cycle marking costs `ceil(ell/L)≤2ell/L` for `ell≥L`. Together with deep-tree
marks this gives `|H|L≤2Q_L`, so a `3L` prefix is sufficient. The original
shifted payload becomes `F^(T-3L)(h)`, with direct unrolling for `T<3L`.
This proves the proposed bound, including `Q_L=0`. Do not optimize while
treating `Q_L` as a constant: it changes with `L`.

The mechanized path-packing lemma instead improves the universal count to
`|H|L≤|S|` with a `2L` prefix. It does not by itself prove the `Q_L` theorem.

## 5. Recognizable target sets: integrated and mechanized

The absorbing transition `G(x)=x` on accepting states and `F(x)` otherwise
has size `O(s+a+n)`. If any target is reached, the first one occurs among
the first `N` distinct trajectory states, at time at most `N-1`. Hence
`G^N(x)` is exactly that first target state on positive inputs, and
`P(G^N(x))` is the desired existence flag. The final `P` test costs `a`,
already absorbed in `A_P`. `Targets.lean` checks the absorbing transition,
eventual-target flag, first-target state, and explicit circuit-size tradeoff.

Here `P` is fixed with the circuit. This theorem does not directly solve
pair-input reachability at the same bound by declaring `P(z)=[z=y]` while
letting `y` vary: making `y` persistent changes the state representation.

The related retraction claim is also correct. `D≥N` because `D` is a
positive multiple of `N`; thus `F^D` maps every state to a cycle, fixes all
cycle states, and is idempotent.

## 6. Small nonlinear controller: valid, not mechanized

The controller must evolve autonomously as `g(u)`. Then the whole sequence
of affine maps applied to the payload is determined by the initial `u`.
Closure under composition gives an affine map for each of the `2^q`
controller values, irrespective of invertibility or commutation.
Tabulate `g^T(u), M_T(u), d_T(u)`, select them using the `q` input bits,
and evaluate the selected matrix-vector product. This proves
`O(2^q(q+p^2))`, up to the usual harmless zero-dimension cases. In the
variable-time version, each conditional stage acts on the current full
state, including its updated controller; this gives the stated factor `m`.

For general transformation families, closure alone is insufficient. Require
every composite to have a representation of bounded length and an evaluation
circuit of bounded cost. Otherwise the representation of a composite could
grow with `T`. The offline composition algorithm need not be efficient for
the fixed-power nonuniform existence statement.

## 7. Almost every power is hard: valid asymptotically

State the result for sufficiently large even `n`. Write `U=2^(n/2)` to
avoid colliding with the upper-bound notation `B`. The group order has
`log2 D ≥ U-1-log2 U`. For a sufficiently small absolute `c`, the number
of size at most `floor(cU/n)` circuits is at most `2^(alpha U)` for some
fixed `alpha<1`. Each circuit computes at most one of the `D` distinct
powers. Thus the exceptional fraction is `2^(-Omega(U))`.

This is a count over residues of the exponent modulo the group order,
not over a distribution of short exponent descriptions. Zero and other
easy exponents remain legitimate exceptions. The argument identifies no
explicit hard exponent and proves no average-case input hardness for a
particular power.

## 8. Fixed remainders: valid in the paper's constant-wire convention

Restricting the power circuit to `(a,0)` gives `T mod a` for `a>0` and zero
at `a=0`. Conversely, on active states, both `b` and `r_T(a)` are below
`a`, so their sum is below `2a`; one comparison and conditional subtraction
suffice. Use a `k+1`-bit sum to retain carry. The inactive branch `a=0` or
`b≥a` returns the original state. This establishes the two inequalities
with `O(n)` additive overhead.

The exact first inequality uses free constant wires when restricting inputs.
In the Lean model constants are gates, so that literal restriction may add
one shared zero gate; asymptotic claims are unchanged. This particular
equivalence has not been formalized. It exposes fixed-integer remainder
functions as the arithmetic objects counted in the lower bound, without
identifying a specific hard integer.

## 9. Deterministic complete configurations: integrated and mechanized

A terminating deterministic trajectory cannot repeat a nonhalting complete
configuration. With `b` bits there are at most `2^b` configurations. Making
halting states absorbing means the `2^b`-th iterate is the final configuration
for every valid initial state, even if the next-state circuit has arbitrary
behavior on invalid encodings. Initialization and output decoding costs add.
`halting_computation` checks this final-configuration contract under semantic
absorption and termination hypotheses, including the bound on the first halt.

Count all persistent information in `b`: input information retained during
the computation, work tapes, control state, and head positions. One cannot
insert an ordinary `n`-bit-input polynomial-space computation with a much
larger configuration into `b=n+O(log n)`. No general PSPACE circuit upper
bound with exponent `n/2` follows.

## 10. AKS and full-space compilation: valid with separate scope

For the fixed-power construction there are `R=O(L+N/L)` records of width
`O(n)`, and `log R=O(n)`. An `O(R log R)` comparator network therefore
reduces sorting cost to `O(n^2 R)`. Other arithmetic and selection costs
fit this bound. This validates the improved `A_2=s+n^2` tradeoff using
[Ajtai--Komlós--Szemerédi's sorting network](https://doi.org/10.1145/800061.808726).
The mechanized construction uses Batcher and proves the `n^3` bound; it
does not mechanize AKS. Its bounded-addition residue algorithm also costs
only `O(Ln^2)`, so arithmetic does not obstruct an eventual AKS replacement.

For compilation, enumerate all `N` states and evaluate `F`; compute finite
graph structure or greedily pack paths; compute the shifted payloads by
transient/cycle arithmetic and residues from the supplied binary exponent;
then emit the fixed circuit templates. These tasks take polynomial time
in `N,s,log(T+2)`. The Batcher construction is explicitly algorithmic; an
AKS-strengthened compiler additionally uses a polynomial-time uniform
sorting-network construction. This is an exponential-time preprocessing
theorem in `n`, not subexponential compilation. The repository contains an
existence formalization, not an implementation or formal proof of this
compiler's time complexity.

## Literature comparison and attribution

[Hirahara, Ilango, and Williams, full version §3.2](https://eccc.weizmann.ac.il/report/2023/171/download)
already use sparse checkpoints, shared circuit lookup, and forward correction
for permutation inversion. Their lookup discussion credits Wolfgang Paul.
Their general-function inversion and compression results have different
contracts; they must not be collapsed into the permutation special case.
The paper retains that attribution and leaves priority of the unrestricted
fixed-power formulation unresolved.

[Munro, Raman, Raman, and Rao](https://arxiv.org/pdf/1108.1983) study succinct
representations of permutations and functions, including powers and inversion
tradeoffs. [Gagie, He, and Navarro](https://users.dcc.uchile.cl/~gnavarro/ps/tcs18.2.pdf)
develop path queries and navigation, including nearest successors with labels
in a range. Identity labels can isolate a singleton target. Their space/time
contracts use stored representations and RAM queries. The proposed comparison
is with total Boolean gate size from a succinct transition circuit, charging
access to every hardwired table. This model distinction is necessary but is
not by itself evidence of novelty.

The formalization credits Mathlib and CSLib, and the author's Circuit library
in Complexitylib for circuit semantics, iteration, wiring, and verified Batcher
sorting and circuit-family counting. Mathlib supplies finite-periodicity
results and the least-common-multiple estimate. This repository adds path
packing, reconstruction, Boolean synthesis and accounting, optimization,
navigation, and the resulting upper and lower bounds. See `lean/README.md` for the pinned
dependencies and exact checked boundary.

## Validation

- `make lean-check`: checked circuits and guarded axiom audits; no additional
  axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
- `make check`: the original independent semantic tests plus exhaustive maps
  through five states, seeded larger examples, all state pairs, all small
  target sets, the packed checkpoint bound, and active-mass coverage.
- `make`: the revised paper, with cross-references resolved; the resulting
  pages are visually inspected separately.

These checks support distinct conclusions. Finite enumeration catches small
semantic mistakes; Lean checks the stated circuit theorem; neither settles
attribution, novelty, or claims outside its explicit scope.
