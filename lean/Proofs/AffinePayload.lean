/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Synthesis
public import Complexitylib.Circuits.SparseSynthesis.Internal.HashCircuit
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Circuits for affine payloads

An affine map on Boolean vectors has a quadratic-size circuit. We identify
its coefficients with the existing affine-hash representation in the user's
circuit library, and reuse that library's charged XOR implementation.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Complexity.PairwiseIndependentHash
open scoped BigOperators

variable {p : ℕ}

/-- The coefficient seed of a Boolean affine map, with its constant column last. -/
def affineMapSeed (a : (Fin p → Bool) →ᵃ[Bool] (Fin p → Bool)) :
    Fin (affineSeedWidth p p) → Bool :=
  affineSeedOfRows fun i => Fin.snoc (fun j => a.linear (Pi.single j 1) i) (a 0 i)

theorem affineMapSeed_eval (a : (Fin p → Bool) →ᵃ[Bool] (Fin p → Bool))
    (v : Fin p → Bool) : affineEval (affineMapSeed a) v = a v := by
  have hlinear : a.linear v = ∑ j, v j • a.linear (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp only [map_sum, map_smul]
  have ha : a v = a.linear v + a 0 := congrFun a.decomp v
  funext i
  have hrows : affineRows (affineMapSeed a) =
      fun i => Fin.snoc (fun j => a.linear (Pi.single j 1) i) (a 0 i) := by
    funext i j
    change Function.uncurry (fun i : Fin p =>
      Fin.snoc (fun j => a.linear (Pi.single j 1) i) (a 0 i))
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  simp only [affineEval, hrows]
  rw [Fin.sum_univ_castSucc]
  simp only [affineAugment, Fin.snoc_castSucc, Fin.snoc_last]
  change (∑ j, a.linear (Pi.single j 1) i * v j) + a 0 i * 1 = a v i
  rw [mul_one]
  rw [ha, hlinear]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Every affine Boolean payload has a concrete De Morgan circuit. -/
theorem affine_payload_circuit (a : (Fin p → Bool) →ᵃ[Bool] (Fin p → Bool)) :
    ∃ c : Circuit Boolean.signature p p,
      c.Computes Boolean.interpretation a ∧ c.size ≤ p * (5 * (p + 1) + 1) := by
  obtain ⟨c, hc, hs⟩ := Complexity.CircuitSparseSynthesis.Internal.exists_hashCircuit
    p p (affineMapSeed a)
  exact ⟨c, fun v => (hc v).trans (affineMapSeed_eval a v), hs⟩

end IteratedFunctions
