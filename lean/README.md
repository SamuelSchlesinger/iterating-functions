# Iterated-function circuits in Lean

This project checks the fixed-power Boolean circuit theorem and its extensions
end to end: square-root optimization, permutation inversion,
variable-time iteration, recognizable targets and halting computations, cycle
labels, reachability and first hitting times, batched evaluation, and the
matching-exponent lower bound. The upper bounds construct actual CSLib
circuits and prove their semantics and native gate counts.

The sparse-counter development also checks a different bound: every signed
fixed power of an `r`-edited counter has at most `100*(n+1)*(r+1)` gates.
This includes the stronger centralizer result and charged coordinate changes.
Streaming division has a checked cost linear in the product of the bit widths.
The small-controller development checks fixed and variable-time powering
for affine payloads, and for general composition-closed payload families
with uniformly bounded circuit cost.

```sh
cd lean
lake exe cache get
lake build --wfail
```

The build checks `Main`, all proof modules in its dependency chain, and the
axiom guards. The cache command is useful on a fresh checkout. Dependency
acquisition requires network access; no local path dependency or preinstalled
copy of the author's projects is needed.

## Public statements

`Statement.lean` imports only CSLib and Mathlib. The foundational budget is

```
powerBudget n s M L = L*s + (n+1)^3 * (L + M/L + 1).
```

For the optimized bounds, write `N = 2^n`, `A = s + (n+1)^3`, and
`B = A + sqrt((n+1)^3 * N * A)`. These square roots are real numbers;
natural-number division in integer budgets means floor division.

| Result | Checked claim |
| --- | --- |
| `fixedPowerBound`, `fixed_power` | Every fixed power has a circuit of size at most `40000 * powerBudget n s N L`, for `1 ≤ L ≤ N`. |
| `fixedPowerOnBound`, `fixed_power_on` | The invariant-set bound replaces `N` in the storage term by `S.card`. |
| `fixed_power_encoded` | For `α : Type u`, an invariant `S : Finset α`, and an encoding into `n` bits injective on `S`, a transition circuit respecting the encoding has circuits for all encoded iterates. |
| `image_sensitive` | Given a circuit `burn` for `F^d`, a circuit for `F^T`, `d ≤ T`, costs at most `burn.size + 40000 * powerBudget n s (image F^d).card L`. |
| `fixed_power_optimized`, `fixed_power_on_optimized` | Real square-root optimization, with constant `120000`, including the invariant-set version. |
| `fixed_power_polynomial` | If `s ≤ K*(n+1)^d`, the circuit size is at most `120000*(K+1)*(n+1)^(max d 3)*2^((n+1)/2)`. |
| `permutation_inverse`, `permutation_inverse_encoded` | Exact inverse circuits with the fixed-power tradeoff, also for injectively encoded finite permutation domains in arbitrary universes. |
| `variable_time`, `variable_time_optimized` | An `m`-bit input exponent, with optimized bound `m*(120000*B + 4*n)`. |
| `variable_time_additive_optimized` | Arbitrarily wide input exponents with bound `33000000*(n+1)*B + 200*m*(n+1)`. Together with the preceding result, this gives the minimum of the two asymptotic bounds. |
| `first_target_state`, `target_reachability` | Eventual recognition of a target predicate and the first visited target state; the absorbing transition costs at most `s + predicate.size + 4*n`. |
| `halting_computation` | Final configurations on valid initial states, under semantic absorption and termination hypotheses, with the original tradeoff and a first halt before `N` steps. |
| `batched_fixed_power_optimized` | For `1 ≤ r ≤ N`, size at most `3000000*(r*A + sqrt((n+1)^3*N*r*A))`. The checkpoint dictionary is shared across the batch. |
| `batched_variable_time_optimized` | Independent `m`-bit exponents for each member; `m` times the preceding batch budget plus `4*r*n` per binary position. |
| `cycle_label_circuit`, `cycle_labels_optimized` | Canonical cycle state, exact cycle length, and phase, for every input; optimized size at most `30120000*B`. |
| `checkpoint_depth_optimized` | Exact transient depth in at most `3000000*B` gates. The earlier binary-search theorem `depth_circuit_optimized` remains available with an extra `(n+1)^2` factor. |
| `reachability_hitting_time` | A circuit on `2*n` input bits returning an existence flag and `n+1` time bits, in at most `300000000*(n+1)*B` gates. On positive instances the decoded time is the first hit and is strictly less than `N`. |
| `first_target_time_optimized` | A target-existence flag and `n+2` first-time bits, with bound `3120000*optimizedBudget n (s+p.size+4*n) N + p.size`. Time is specified only on positive instances and is less than `N`. |
| `halting_time` | Under semantic absorption and termination, exact first halting times on valid initial states, with bound `3000000*B`. No recognizer circuit is needed. |
| `visit_schedule_optimized` | A complete visit descriptor on pair inputs: one success flag, `n+1` first-time bits, and `n+1` period bits, with bound `360000000*(n+1)*B`. Period zero encodes a singleton. The theorem specifies all visit times and the number through every deadline. The deadline arithmetic is a semantic interpretation, not an additional circuit-size claim. |
| `matching_lower_bound` | For `k ≥ 64`, a Boolean permutation circuit on `2*k` bits of size at most `50*(k+1)` has a power for which every implementing circuit has more than `2^k/(1024*(k+1))` gates. The division is integral. |
| `almost_every_counter_power` | For `k ≥ 64`, the number of exponent residues with circuits of size at most `lowerBudget k`, times `2^(2^(k-1))`, is at most the period. Thus the easy fraction is at most `2^(-2^(k-1))`. |
| `ModulusCounter.remainder_of_power` / `power_of_remainder` | Convert a power circuit to `a ↦ T mod a` (zero at modulus zero) with one extra gate, or convert a remainder circuit to a power with at most `100*(k+1)` extra gates. |
| `ModulusCounter.hard_power_exponent_capacity` | If `T < 2^m` and its power exceeds `lowerBudget k`, then `2^k < 112640*(m+1)*(k+1)^2`. The proof constructs a power circuit of size at most `110*(m+1)*(k+1)`. |
| `sparse_counter_centralizer` | If an injective word map `H` commutes with `F`, and `F` differs from increment at `r` inputs, a circuit for `H` has at most `100*(n+1)*(r+1)` gates. `F` need not be a permutation. |
| `sparse_counter_power` | The same bound for every integer power of a permutation, including negative powers. |
| `sparse_coordinate_power` | If a permutation `G` becomes increment under a bijection `e`, every fixed signed power of an `r`-edited `G` costs at most `encode.size + decode.size + 100*(n+1)*(r+1)`. Both coordinate circuits and their semantics are supplied and charged. |
| `synchronous_coalescence_optimized` | On a pair `(x,y)`, decides whether equal-time iterates ever meet, with bound `240000*B + 6*n + 1`. |
| `recurring_target_optimized` | Decides acceptance at arbitrarily large times; the bound is `240000*optimizedBudget n (s+p.size+4*n) N + p.size`. |
| `eventually_always_target_optimized` | Decides permanent eventual acceptance; replace `p.size` by `p.size+1` in the preceding budget and add `p.size+2` outside it. |
| `bounded_modulus_remainder` | An `m`-bit numerator modulo a nonzero `k`-bit input modulus has a circuit of size at most `2 + m*(51*(k+1)+4)`. The circuit is total; the specification requires a positive modulus. |
| `active_mass_fixed_power` | For `1 ≤ L ≤ 2^n`, a power circuit has size at most `120000*powerBudget n s Q_L L`, where `Q_L` counts states of depth at least `L` and vertices of cycles of length at least `L`. |
| `controlled_family_power` | For an autonomous `q`-bit controller and `p`-bit payload, a composition-closed family containing identity and having circuit bound `K` gives every fixed power a circuit of size at most `2 + 2^q*(K + 6*q + 4*p + 1)`. |
| `controlled_family_variable_time` | An `m`-bit exponent multiplies the preceding bound, plus `4*(q+p)` conditional-selection gates per stage, by `m`. |
| `affine_controller_power` | Arbitrary Boolean affine payload maps give bound `D = 2 + 2^q*(p*(5*(p+1)+1) + 6*q + 4*p + 1) ≤ 32*2^q*(q+p^2+1)`. Neither injectivity nor commutation is required. |
| `affine_controller_polynomial` | If `2^q ≤ K*(q+p+1)^d`, every fixed power has a circuit of size at most `32*K*(q+p+1)^(d+2)`. |
| `affine_controller_variable_time` | The affine-controller iterator with an `m`-bit time input has at most `m*(D + 4*(q+p))` gates. |

The explicit constants are loose accounting bounds, not practical circuit-size
estimates. The `+1`s cover zero-width encodings and empty invariant sets.
The lower-bound exponent is existential and lies below
`lcm(1,...,2^k-1)`; the theorem does not identify a short hard exponent.
The navigation time field is unspecified on unreachable pairs.

## Circuit model and universes

The native circuit type is `Cslib.Circuits.Circuit Boolean.signature n m`.
The basis has Boolean constants, NOT, AND, and OR. `size` counts every gate,
including constants. Input and output wiring, copying wires, and fanout are
free. A fixed change of complete fan-in-two basis changes the bounds by an
absolute factor. Arithmetic, lookup, and multiplexing are synthesized into
Boolean gates and are charged.

The packing and reconstruction lemmas quantify over any `α : Type u`, with
no finiteness requirement on the ambient type. The encoded theorem assumes
injectivity only on the finite invariant set `S`; states outside `S` can
share encodings. It starts with encoded inputs and returns encoded outputs.
Initialization and decoding circuits must be charged separately.

The orbit, phase, and hitting-time identities in `OrbitStructure.lean`,
`CycleLabels.lean`, `HittingTimes.lean`, and `Navigation.lean` are also
universe polymorphic. They assume a finite type; cardinality bounds use
`Fintype`, and canonical representatives use a linear order. The native
navigation circuit statements specialize to bit states. They do not count
arbitrary operations on a finite type as unit-cost gates. Unrolling and
retained-orbit lemmas are additionally polymorphic in circuit signatures
and interpretation carriers. The commutation-defect containment is valid on
arbitrary types without finiteness; its cardinality and relabeling lemmas use
finite types in arbitrary universes. Sparse-counter circuit statements use
`BitVec n` coordinates with the same native Boolean gate model.
The controlled-product and payload-closure identities quantify independently
over controller and payload types in arbitrary universes, without finiteness.
The corresponding gate bounds use Boolean encodings and enumerate only the
controller states. The affine specialization uses Mathlib's `AffineMap` over
the Boolean ring, keeping payload vectors and Boolean wires in the same type.

## Proof choices

1. **Pack paths and retain wires.** `Checkpoints.lean` removes disjoint simple
   paths of `L` vertices and marks their endpoints, proving
   `H.card * L ≤ S.card`. A short prefix either repeats or reaches a checkpoint.
   CSLib `Synthesis` shares intermediate wires and adds construction costs.
2. **Find one witness for fixed powers.** `Records.lean`, `Collisions.lean`,
   and `Detector.lean` sort checkpoints, prefix states, and tagged padding.
   An adjacent equal-key pair with distinct nonpadding records supplies a
   checkpoint hit or a genuine repeated pair. Batcher sorting semantics and
   routing come from the Circuit library; Boolean comparator costs are proved
   here. The repeated-interval decoder adds a hardwired residue's period at
   most `2*L` times, within the cubic polynomial allowance.
3. **Optimize and compose.** `Optimization.lean` proves an integer choice of
   `L` and the real square-root inequality. `Applications.lean` uses factorial
   exponents for inversion and cyclicity. `VariableTime.lean` conditionally
   applies binary powers. `FiniteOrbit.lean` and `Targets.lean` prove the
   first-target and absorbing-halting reductions.
4. **Share an entire dictionary for batches.** `BatchLookup.lean` verifies
   multiquery lookup, including absent keys and repeated queries, with a
   Batcher-based routing cost. `BatchPowers.lean` shares the checkpoint table
   and retains a repetition fallback for each member. `BatchVariableTime.lean`
   repeats this construction once per exponent bit.
5. **Compute labels on cycles.** The label circuit first applies `F^(N!)`.
   This reaches the cycle and preserves the representative, period, and phase.
   A short cyclic prefix with no checkpoint contains a whole cycle, so a scan
   suffices to find its minimum state and first positive return. Checkpoint
   hits use a shared label dictionary and a modular phase correction. This
   differs from the manuscript's direct first-repetition proof while giving
   the same asymptotic bound. The order is lexicographic from coordinate zero.
6. **Compare projected orbits, then navigate.** `CheckpointDepth.lean` compares
   the original and projected short orbits. Their first agreement is cycle
   entry; without agreement, a checkpoint's stored depth plus its prefix index
   is exact. One dictionary suffices, giving `O(B)` gates. The earlier
   `BinarySearch.lean` and `DepthCircuit.lean` provide a separate weaker route.
   `NavigationSynthesis.lean` combines two depths,
   two cycle labels, the transient-depth difference test, and the cyclic phase
   formula. `NavigationCircuits.lean` proves the final flag, first-hit
   semantics, and size. Labels and arithmetic use `n+3` bits internally; the
   public time output uses `n+1`. The remaining variable-time call gives the
   `O(nB)` bound. Its proved time bound `< 2^n` permits dropping
   the high bit on positive instances. `Division.lean` proves a total
   shift-and-subtract remainder circuit costing `O(n^3)` gates.
7. **Count actual circuit descriptions.** `ModulusCounter.lean` proves the
   exact powers and their distinctness below the least common multiple.
   `CounterCircuit.lean` synthesizes the linear-size update, using a shared
   carry chain. `CircuitCounting.lean` bounds Boolean circuit descriptions,
   including output wires. `LowerBound.lean` combines this with Mathlib's
   least-common-multiple lower bound and the Circuit library's finite-family
   counting theorem. The final result quantifies over actual native circuits.

8. **Exploit sparse displacement.** `CommutationDefect.lean` proves the
   factor-two defect estimate and invariance of edit counts under conjugation.
   `SparseDisplacement.lean` telescopes the displacement derivative over its
   finite support. Each selected correction is charged once, with shared carry
   chains in `LinearArithmetic.lean`. No lookup or arithmetic primitive is free.
   Permutation group integer powers give the signed-power theorem. Supplied
   encoder and decoder circuits transfer it to other orbit coordinates.
9. **Stream long numerators.** `StreamingRemainder.lean` recursively processes
   time bits from most significant to least significant. One spare bit keeps
   twice the current remainder from overflowing. Linear subtraction, comparison,
   and selection give `51*w+4` gates per bit at working width `w`. The public
   remainder circuit returns `k` bits and uses `k+1` working bits.

10. **Query the eventual dynamics.** `CycleProjection.lean` proves that
    `F^(N!)` is an idempotent retraction fixing exactly the cyclic states, and
    the two orbits agree exactly from transient depth onward. Its coalescence
    lemma uses injectivity of iteration on periodic points. `EventualQueries.lean`
    supplies actual pair-input coalescence circuits, recurring-target circuits,
    and permanent-acceptance circuits with optimized gate bounds. The projection
    layer also checks time normalization below `2*N`. `LongTime.lean` connects
    it to cycle-label circuits and streaming remainders, then powers with only
    `n+3` internal time bits. All widths and gate costs are checked, giving
    additive dependence on the original time width.
11. **Recover first target times.** `TargetTimes.lean` proves that, when a
    target is reached, its first visit time is the transient depth of the
    absorbing map. The proof cancels iteration on cyclic states. Composing
    the absorbing transition, checkpoint depth, and target flag gives the
    native first-time circuit. Semantic absorption and termination similarly
    yield halting times without a recognizer cost. These dynamics lemmas use
    `Finite` types in arbitrary universes.
12. **Describe all visits.** `VisitSchedules.lean` proves that visits after the
    first occur at exactly the multiples of the target's minimal return
    period. This identity needs no finiteness assumption. `VisitCounts.lean`
    proves the bounded counting formula, treating period zero separately.
    `VisitScheduleCircuits.lean` synthesizes a zero-off-cycle period field
    and appends it to the navigation result, with correctness for every time
    and deadline. No enumeration of the visit set is needed.
13. **Quantify hard powers and their arithmetic content.** `TypicalPowers.lean`
    counts easy exponent residues with an explicit exponential margin. Its
    division-free count is equivalent to the finite uniform probability bound.
    `CounterRemainders.lean` constructs both directions of the remainder
    comparison, preserving carry and charging the restriction's shared zero.
    `ExponentLength.lean` combines the linear arithmetic with the gate lower
    bound to force exponential description length for hard exponents.
14. **Charge only long trajectories.** `ActiveCheckpoints.lean` packs paths
    inside the deep/long-cycle set, proving `|H|*L ≤ Q_L` and coverage within
    `4L` steps. The charged set need not be invariant. `ActivePowers.lean`
    uses `n+3` index bits and the existing reconstruction to obtain an actual
    circuit bound, including `Q_L=0`. The count depends on `L` throughout.
15. **Separate a small controller from a closed payload family.**
    `ControlledMaps.lean` proves the semantic composition invariant and
    synthesizes every candidate payload circuit, then shares controller
    equality flags across a record-selection scan. Its uniform evaluation
    budget applies to all composite maps, not just the individual updates.
    `AffinePayload.lean` expresses an affine map as the coefficient seed
    used by the Circuit library's affine-hash circuitry and reuses its
    four-gate XOR implementation. `AffineController.lean` specializes the
    generic theorem, proves the polynomial bound, and uses the general
    conditional binary-powering theorem in `VariableTime.lean` for input
    exponents. Each stage updates both controller and payload.

The construction uses classical choices of checkpoints, finite enumerations,
and circuit witnesses. It establishes nonuniform existence, not an extracted
compiler or a preprocessing-time guarantee. For halting computations, the
state width includes all persistent input, control, and workspace bits.

## Trusted boundary and remaining scope

`Main.lean` guards the axiom lists of the principal public results. Each list
contains exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no
`sorry` placeholders, added axioms, or `native_decide` steps in the project.
Kernel checking does not establish statement fidelity or historical novelty.

The sparse arc-chart construction and its full additive live-time bound are
proved in the manuscript and implemented in `../sparse_counter.py`, but the
chart's existence and gate-count bridge are not yet checked in Lean. Its
streaming-arithmetic ingredient is checked. The sparse-transition counting
application and the finite-field corollary, including the use of the external
discrete-logarithm theorem, are also outside the current Lean boundary.

The AKS polynomial improvement and full-state-space effective compiler are
still proposals in `REVIEW.md`, not separately formalized or asserted as
theorems in the manuscript. The paper's cryptographic discussion
and literature comparisons remain prose arguments.

Pinned dependencies, also recorded in the Lake manifest:

- Lean `v4.35.0-rc3`.
- [Mathlib](https://github.com/leanprover-community/mathlib4/tree/728a93eeff833da3173895bb0575752fdc24edb0), revision `728a93eeff833da3173895bb0575752fdc24edb0`.
- [CSLib](https://github.com/leanprover/cslib/tree/311d27ad8458b61e9b7461fc83a480e4be97aef2), revision `311d27ad8458b61e9b7461fc83a480e4be97aef2`.
- [Complexitylib / Circuit](https://github.com/SamuelSchlesinger/complexitylib/tree/add0aca8ee0d71e68969f2cb45cf91554a50f787), revision `add0aca8ee0d71e68969f2cb45cf91554a50f787`.

The project follows the statement/proof/Main separation and guarded axiom
checks of the author's `circuit-lbs/circuit-lb-4.56-lean` development. Circuit
semantics, iteration, routing, Batcher network proofs, and finite-family
counting are credited to the CSLib and Complexitylib contributors. Finite
periodicity and the least-common-multiple estimate use Mathlib. This project
adds the checkpoint constructions, Boolean synthesis and accounting,
reconstruction, navigation, optimization, and their applications. See the
paper for Batcher and the checkpoint/inversion literature.
