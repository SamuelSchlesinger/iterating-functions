/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.NavigationSynthesis
public import Proofs.NavigationFeatures
public import Proofs.ForestCircuits

/-! # Reachability and first-hitting-time circuits -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
variable {n : ℕ}
noncomputable local instance navigationCircuitsStateOrder : LinearOrder (State n) := stateOrder n

def navigationBudget (n s L : ℕ) : ℕ :=
  1 + 72080000 * powerBudget n s (2 ^ n) L + 1000 * (n + 4) ^ 3

/-- Forest reachability plus depths, cycle labels, and word arithmetic. -/
theorem navigation_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + n) (1 + (n + 1)),
      out.Computes Boolean.interpretation (fun z =>
        navigationBits (c.eval Boolean.interpretation) (inputLeft z) (inputRight z)) ∧
      out.size ≤ navigationBudget n c.size L := by
  let f := c.eval Boolean.interpretation
  let x : State (n + n) → State n := inputLeft
  let y : State (n + n) → State n := inputRight
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit c L hL hLN
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  obtain ⟨reach, hr, hrs⟩ := forest_reachability_circuit c L hL hLN
  have hle : labels.eval Boolean.interpretation = canonicalLabel f := funext hl
  let src := inputs (n + n) ∪ {fun _ => false}
  have hx : wires x ⊆ src := by rintro _ ⟨bit, rfl⟩; exact Or.inl ⟨_, rfl⟩
  have hy : wires y ⊆ src := by rintro _ ⟨bit, rfl⟩; exact Or.inl ⟨_, rfl⟩
  have hdx := synthesis_depthWord depth f hd src x hx (Or.inr rfl)
  have hdy := synthesis_depthWord depth f hd src y hy (Or.inr rfl)
  have hlx : Synthesis Boolean.interpretation src (wires (fun z => canonicalLabel f (x z)))
      labels.size := by
    simpa only [hle, wires] using Synthesis.circuit (I := Boolean.interpretation) (s := src)
      labels x (fun bit => hx ⟨bit, rfl⟩)
  have hly : Synthesis Boolean.interpretation src (wires (fun z => canonicalLabel f (y z)))
      labels.size := by
    simpa only [hle, wires] using Synthesis.circuit (I := Boolean.interpretation) (s := src)
      labels y (fun bit => hy ⟨bit, rfl⟩)
  have hreach := Synthesis.circuit (I := Boolean.interpretation) (s := src) reach id
    (fun bit => Or.inl ⟨bit, rfl⟩)
  have hfeatures := (((hdx.union hdy).union hlx).union hly).union hreach
  let all := src ∪ ((wordWires (fun z => depthWord f (x z)) ∪
    wordWires (fun z => depthWord f (y z)) ∪ wires (fun z => canonicalLabel f (x z)) ∪
    wires (fun z => canonicalLabel f (y z))) ∪ wires (reach.eval Boolean.interpretation))
  have avx : wires (fun z => canonicalLabel f (x z)) ⊆ all :=
    fun _ h => Or.inr (Or.inl (Or.inl (Or.inr h)))
  have avy : wires (fun z => canonicalLabel f (y z)) ⊆ all :=
    fun _ h => Or.inr (Or.inl (Or.inr h))
  have decode (init : State (n + n) → State n)
      (hav : wires (fun z => canonicalLabel f (init z)) ⊆ all) :
      wordWires (fun z => lengthWord f (init z)) ⊆ all ∧
      wordWires (fun z => phaseWord f (init z)) ⊆ all := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨bit, rfl⟩
      simpa only [canonicalLabel, labelBits, lengthWord, Fin.append_right, Fin.append_left] using
        hav ⟨Fin.natAdd n (Fin.castAdd (n + 3) bit), rfl⟩
    · rintro _ ⟨bit, rfl⟩
      simpa only [canonicalLabel, labelBits, phaseWord, Fin.append_right] using
        hav ⟨Fin.natAdd n (Fin.natAdd (n + 3) bit), rfl⟩
  have hre : (fun z => reach.eval Boolean.interpretation z 0) =
      (fun z => navigationFlag f (x z) (y z)) := by
    funext z
    apply Bool.eq_iff_iff.mpr
    rw [navigationFlag_spec, reaches_iff]
    exact hr z
  have avFlag : (fun z => navigationFlag f (x z) (y z)) ∈ all := by
    rw [← hre]
    exact Or.inr (Or.inr ⟨0, rfl⟩)
  have hnav := synthesis_navigation_given_flag f all x y avFlag
    (fun _ h => Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h)))))
    (fun _ h => Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    (decode x avx).1 (decode x avx).2 (decode y avy).2
  have h := (Synthesis.const (s := inputs (n + n)) false).trans
    (hfeatures.trans hnav)
  obtain ⟨out, hout, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, hout, hs.trans ?_⟩
  unfold navigationBudget
  lia

/-- Every component fits the original fixed-power tradeoff. -/
theorem navigationBudget_le (n s L : ℕ) :
    navigationBudget n s L ≤ 100000000 * powerBudget n s (2 ^ n) L := by
  have hb : (n + 1) ^ 3 ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    have h := Nat.mul_le_mul_left ((n + 1) ^ 3)
      (show 1 ≤ L + 2 ^ n / L + 1 by lia)
    lia
  have hfour : (n + 4) ^ 3 ≤ 64 * (n + 1) ^ 3 := by
    have h := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by lia) 3
    nlinarith
  have hpoly : 1 + 1000 * (n + 4) ^ 3 ≤
      65000 * powerBudget n s (2 ^ n) L := by
    nlinarith [Nat.zero_le (n ^ 3)]
  unfold navigationBudget
  lia

/-- Reachability and first hitting time, with an explicit optimized gate bound. -/
theorem reachability_hitting_time (c : Circuit Boolean.signature n n) :
    ∃ out : Circuit Boolean.signature (n + n) (1 + (n + 1)),
      (∀ z, out.eval Boolean.interpretation z 0 = true ↔
        ∃ t, (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z) ∧
      (∀ z, out.eval Boolean.interpretation z 0 = true →
        let t := (word fun i : Fin (n + 1) =>
          out.eval Boolean.interpretation z (Fin.natAdd 1 i)).toNat
        (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z ∧
          (∀ j < t, (c.eval Boolean.interpretation)^[j] (inputLeft z) ≠ inputRight z) ∧
          t < 2 ^ n) ∧
      (out.size : ℝ) ≤ 300000000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, ho⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := navigation_circuit c L hL hLN
  refine ⟨out, ?_, ?_, ?_⟩
  · intro z
    rw [hout z]
    exact navigationBits_flag _ _ _
  · intro z hz
    rw [hout z] at hz ⊢
    exact navigationBits_time _ _ _ ((navigationBits_flag _ _ _).mp hz)
  · have hs' : (out.size : ℝ) ≤
        100000000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
      exact_mod_cast hs.trans (navigationBudget_le n c.size L)
    linarith

end IteratedFunctions
