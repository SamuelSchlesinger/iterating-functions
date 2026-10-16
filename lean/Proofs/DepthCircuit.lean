/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.BinarySearch
public import Proofs.Applications
public import Proofs.OrbitStructure

/-! # A circuit for exact transient depth -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
variable {n : ℕ}

def depthBudget (n s L : ℕ) : ℕ :=
  2 + (n + 1) * ((n + 2) * (40000 * powerBudget n s (2 ^ n) L + 4 * n) +
    (40000 * powerBudget n s (2 ^ n) L + (6 * n + 1)) + 100 * (n + 3) ^ 2)

theorem depth_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n (n + 2),
      (∀ x, word (out.eval Boolean.interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval Boolean.interpretation) x)) ∧
      out.size ≤ depthBudget n c.size L := by
  let f := c.eval Boolean.interpretation
  obtain ⟨cyclic, hcyc, hcs⟩ := cyclicity_circuit c L hL hLN
  let constants : Set (State n → Bool) := {fun _ => false, fun _ => true}
  let src := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : State n => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let C := (n + 2) * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n) + cyclic.size
  have query (s : Set (State n → Bool)) (hs : src ⊆ s)
      (value : State n → BitVec (n + 2)) (hv : wordWires value ⊆ s) :
      Synthesis Boolean.interpretation s
        {fun x => decide (transientDepth f x ≤ (value x).toNat)} C := by
    have hi := synthesis_variable_time c s id (fun x i => (value x).getLsbD i.val)
      (fun _ h => hs (Or.inl h)) (fun i => hv ⟨i, rfl⟩) L hL hLN
    simp only [binaryValue_bits] at hi
    let current := fun x => f^[(value x).toNat] x
    have hq := Synthesis.circuit (I := Boolean.interpretation) (s := s ∪ wires current) cyclic
      current (fun bit => Or.inr ⟨bit, rfl⟩)
    have he (x : State n) : cyclic.eval Boolean.interpretation (current x) 0 =
        decide (transientDepth f x ≤ (value x).toNat) := by
      apply Bool.eq_iff_iff.mpr
      rw [hcyc, periodic_iterate_iff, decide_eq_true_eq]
    exact (hi.trans hq).mono Set.Subset.rfl
      (by rintro g rfl; exact ⟨0, funext he⟩) le_rfl
  have h := hconst.trans (synthesis_threshold src (transientDepth f) n C
    (fun x => by simpa using transientDepth_lt_card f x) hc query)
  obtain ⟨out, hout, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, fun x => ?_, hs.trans ?_⟩
  · rw [hout x, word_bits]
  · unfold depthBudget
    dsimp only [C]
    have hh := Nat.mul_le_mul_left (n + 1) hcs
    lia

/-- The threshold search introduces at most a quadratic factor. -/
theorem depthBudget_le (n s L : ℕ) (hL : 0 < L) :
    depthBudget n s L ≤ 1000000 * (n + 1) ^ 2 * powerBudget n s (2 ^ n) L := by
  have hb : (n + 1) ^ 3 ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    have h := Nat.mul_le_mul_left ((n + 1) ^ 3)
      (show 1 ≤ L + 2 ^ n / L + 1 by lia)
    lia
  have hp : 4 * n * (n + 2) + (6 * n + 1) + 100 * (n + 3) ^ 2 ≤
      1000 * (n + 1) ^ 3 := by nlinarith [Nat.zero_le (n ^ 3)]
  have hcost := Nat.mul_le_mul_left (n + 1) hp
  have hb' := Nat.mul_le_mul_left (n + 1) hb
  have hB : 1 ≤ powerBudget n s (2 ^ n) L :=
    (by nlinarith [Nat.zero_le (n ^ 3)] : 1 ≤ (n + 1) ^ 3).trans hb
  unfold depthBudget
  nlinarith [Nat.zero_le (n ^ 2 * powerBudget n s (2 ^ n) L)]

theorem depth_circuit_optimized (c : Circuit Boolean.signature n n) :
    ∃ out : Circuit Boolean.signature n (n + 2),
      (∀ x, word (out.eval Boolean.interpretation x) =
        BitVec.ofNat (n + 2) (transientDepth (c.eval Boolean.interpretation) x)) ∧
      (out.size : ℝ) ≤ 3000000 * (n + 1 : ℝ) ^ 2 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, ho⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := depth_circuit c L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤
      1000000 * (n + 1 : ℝ) ^ 2 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs.trans (depthBudget_le n c.size L hL)
  have h := mul_le_mul_of_nonneg_left ho (show 0 ≤ 1000000 * (n + 1 : ℝ) ^ 2 by positivity)
  nlinarith

end IteratedFunctions
