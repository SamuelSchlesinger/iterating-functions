# Fixed-power circuits in Lean

This project proves the fixed-power Boolean circuit tradeoff end to end,
including circuit existence, evaluation correctness, and gate count. It also
proves the invariant-set and image-sensitive extensions and transport to encoded
state spaces in arbitrary Lean universes.

```sh
cd lean
lake exe cache get
lake build --wfail
```

`lake build --wfail` builds `Main`, all proof modules in its dependency chain,
and the guarded axiom checks. The first command downloads the Mathlib cache on
a fresh checkout. Normal Lake dependency acquisition requires network access.
No local path dependency or preinstalled copy of the author's projects is needed.

## Public statements

`Statement.lean` imports only CSLib and Mathlib. With

```
powerBudget n s M L = L*s + (n+1)^3 * (L + M/L + 1),
```

the exported results in `Main.lean` are:

| Result | Checked claim |
| --- | --- |
| `fixedPowerBound`, `fixed_power` | Every fixed power has a Boolean circuit of size at most `40000 * powerBudget n c.size (2^n) L`, for `1 ≤ L ≤ 2^n`. |
| `fixedPowerOnBound`, `fixed_power_on` | The same result on a finite invariant set `S`, replacing `2^n` in the budget by `S.card`. |
| `fixed_power_encoded` | For `α : Type u`, finite invariant `S : Finset α`, and an encoding into `n` bits injective on `S`, the circuit computes the encoded iterate. The given transition circuit must respect that encoding on `S`. |
| `image_sensitive` | Given a circuit `burn` computing `F^d`, a circuit for `F^T`, `d ≤ T`, has size at most `burn.size + 40000 * powerBudget n c.size |image(F^d)| L`. |

The division in the budget is natural-number division. The `+1`s cover empty
sets and zero-width encodings. The constant is intentionally loose. The real
square-root optimization is proved in the paper; it is not a separate Lean
theorem. The navigation, variable-time, batched, and lower-bound results are also
outside this formalization.

## Circuit model and universes

The circuit type is `Cslib.Circuits.Circuit Boolean.signature n n`.
The basis has Boolean constants, NOT, AND, and OR. Native `size` counts every
gate, including constants. Input and output wiring, copying wires, and fanout
are free. Constants are shared by generating false and true once. A fixed
change from the paper's complete fan-in-two basis changes bounds by an absolute
factor. Encoding and decoding work is not silently included or free: the
encoded theorem starts with encoded inputs and returns encoded outputs.

The graph lemmas quantify over any `α : Type u`, with no finiteness requirement
on the ambient type. `fixed_power_encoded` assumes injectivity only on `S`;
states outside `S` can share encodings. It continues to count Boolean gates
and uses the specified bit width. It does not treat an arbitrary state operation
as a unit-cost gate. The unrolling and retained-orbit lemmas are additionally
polymorphic in circuit signatures and interpretation carriers.

## Proof choices

1. **Pack paths.** `Checkpoints.lean` removes disjoint simple paths of `L`
   vertices and marks their endpoints. The resulting set satisfies
   `H.card * L ≤ S.card`. Any simple prefix meets a packed path and reaches its
   endpoint before `2*L` steps. This avoids developing cycle decompositions.
2. **Share wires.** CSLib `Synthesis` composes gate bounds while retaining
   intermediate wires. `Iteration.lean` charges one transition circuit per
   prefix step. `Sorting.lean` builds shared Boolean comparators and uses the
   Circuit library's Batcher sorting correctness and record-permutation proofs.
3. **Sort once.** `Records.lean`, `Collisions.lean`, and `Detector.lean` show that
   one adjacent equal-state collision between distinct nonpadding records
   supplies either a checkpoint hit or a genuine repeated pair. This avoids
   formalizing the full batched dictionary API when one witness is enough.
4. **Use bounded words.** `Words.lean`, `Arithmetic.lean`, and `Residues.lean`
   prove gate bounds and word semantics. Given a repeated interval `[i,j)`, add
   `j-i` to the hardwired residue `T % (j-i)` until reaching the interval.
   At most `2*L` corrections suffice. Width `n+2` prevents overflow on valid
   witnesses; all branches are total on arbitrary inputs. The circuit pays
   `O(L*n^2)` for these corrections, within the main `O(L*n^3)` allowance.
5. **Assemble and account.** `DecoderCircuits.lean` and `Construction.lean`
   synthesize the total output function. `FixedPower.lean` proves its agreement
   with the iterate on `S` and the explicit final bound. `Extensions.lean`
   transports the result to encodings and images.

The proof uses classical choices of checkpoints, finite enumerations, and
circuit witnesses. It establishes nonuniform existence, not an extracted
compiler or a preprocessing-time guarantee.

## Trusted boundary and dependencies

`Main.lean` guards the axiom lists of all four public claims. Each list contains
exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`
placeholders, added axioms, or `native_decide` steps. The kernel checks the
proofs; statement fidelity and historical novelty remain mathematical review
questions.

Pinned dependencies, also recorded in the Lake manifest:

- Lean `v4.35.0-rc3`.
- [Mathlib](https://github.com/leanprover-community/mathlib4/tree/728a93eeff833da3173895bb0575752fdc24edb0), revision `728a93eeff833da3173895bb0575752fdc24edb0`.
- [CSLib](https://github.com/leanprover/cslib/tree/311d27ad8458b61e9b7461fc83a480e4be97aef2), revision `311d27ad8458b61e9b7461fc83a480e4be97aef2`.
- [Complexitylib / Circuit](https://github.com/SamuelSchlesinger/complexitylib/tree/add0aca8ee0d71e68969f2cb45cf91554a50f787), revision `add0aca8ee0d71e68969f2cb45cf91554a50f787`.

The project follows the statement/proof/Main separation and guarded axiom
checks of the author's `circuit-lbs/circuit-lb-4.56-lean` development. Circuit
semantics, iteration, routing, and Batcher network proofs are credited to the
CSLib and Complexitylib contributors; this project adds the checkpoint,
reconstruction, shared Boolean synthesis, and final tradeoff proofs. See the
paper for Batcher and the checkpoint/inversion literature.
