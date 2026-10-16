/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Function.Iterate

/-!
# Statements for fixed-power circuit bounds

This review boundary imports only CSLib and Mathlib. The circuit model has free
input and output wires, arbitrary fanout, and the De Morgan basis. Its native
size charges constants; sharing the two constants costs at most two gates
compared with a free-constant convention over this basis. A fixed change of
Boolean basis changes size by a constant factor.

`FixedPowerOnBound` is the stronger invariant-set claim. Arbitrary state types
can be represented injectively by bit strings, in any Lean universe; no gate
that evaluates an arbitrary state transition at unit cost is introduced.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

/-- The bit representation used by a circuit with `n` inputs and outputs. -/
abbrev State (n : ℕ) := Fin n → Bool

/-- The natural-number tradeoff, with harmless `+1`s covering empty and zero-width cases. -/
def powerBudget (n s M L : ℕ) : ℕ :=
  L * s + (n + 1) ^ 3 * (L + M / L + 1)

/-- Every fixed power of a Boolean endomorphism has the stated circuit tradeoff. -/
def FixedPowerBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) (c : Circuit Boolean.signature n n) (T L : ℕ),
    0 < L → L ≤ 2 ^ n →
    ∃ d : Circuit Boolean.signature n n,
      d.Computes Boolean.interpretation (c.eval Boolean.interpretation)^[T] ∧
      d.size ≤ C * powerBudget n c.size (2 ^ n) L

/-- The tradeoff depends on the size of a finite invariant set, using the original
bit representation and correctness restricted to that set. -/
def FixedPowerOnBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) (c : Circuit Boolean.signature n n) (S : Finset (State n))
    (T L : ℕ),
    (∀ x ∈ S, c.eval Boolean.interpretation x ∈ S) →
    0 < L → L ≤ 2 ^ n →
    ∃ d : Circuit Boolean.signature n n,
      d.ComputesOn Boolean.interpretation S (c.eval Boolean.interpretation)^[T] ∧
      d.size ≤ C * powerBudget n c.size S.card L

end IteratedFunctions
