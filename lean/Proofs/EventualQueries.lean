/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CycleProjection
public import Proofs.Targets

/-! # Circuits for synchronous coalescence and recurring target predicates -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n : ℕ}

theorem synchronous_coalescence (c : Circuit Boolean.signature n n)
    (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + n) 1,
      (∀ z, out.eval Boolean.interpretation z 0 = true ↔
        ∃ t, (c.eval Boolean.interpretation)^[t] (fun i => z (Fin.castAdd n i)) =
          (c.eval Boolean.interpretation)^[t] (fun i => z (Fin.natAdd n i))) ∧
      out.size ≤ 80000 * powerBudget n c.size (2 ^ n) L + 6 * n + 1 := by
  let f := c.eval Boolean.interpretation
  obtain ⟨power, hp, hs⟩ := fixed_power n c (2 ^ n) L hL hLN
  let left := fun z : State (n + n) => fun i : Fin n => z (Fin.castAdd n i)
  let right := fun z : State (n + n) => fun i : Fin n => z (Fin.natAdd n i)
  let a := fun z => power.eval Boolean.interpretation (left z)
  let b := fun z => power.eval Boolean.interpretation (right z)
  have ha := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (n + n)) power left
    (fun i => ⟨_, rfl⟩)
  have hb := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (n + n)) power right
    (fun i => ⟨_, rfl⟩)
  have heq := synthesis_bits_eq (inputs (n + n) ∪ (wires a ∪ wires b)) a b
    (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr (Or.inr h))
  obtain ⟨out, ho, hsize⟩ := ((ha.union hb).trans heq).exists_circuit
  refine ⟨out, fun z => ?_, by lia⟩
  rw [ho z]
  change decide (a z = b z) = true ↔ _
  rw [decide_eq_true_eq]
  simp only [a, b]
  rw [hp, hp]
  simpa only [show Fintype.card (State n) = 2 ^ n by simp] using
    (eventual_coalescence_iff f (left z) (right z)).symm

theorem synchronous_coalescence_optimized (c : Circuit Boolean.signature n n) :
    ∃ out : Circuit Boolean.signature (n + n) 1,
      (∀ z, out.eval Boolean.interpretation z 0 = true ↔
        ∃ t, (c.eval Boolean.interpretation)^[t] (fun i => z (Fin.castAdd n i)) =
          (c.eval Boolean.interpretation)^[t] (fun i => z (Fin.natAdd n i))) ∧
      (out.size : ℝ) ≤ 240000 * optimizedBudget n c.size (2 ^ n) + 6 * n + 1 := by
  obtain ⟨L, hL, hLN, hopt⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := synchronous_coalescence c L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤
      80000 * (powerBudget n c.size (2 ^ n) L : ℝ) + 6 * n + 1 := by exact_mod_cast hs
  linarith

/-- A fixed recognizable target recurs arbitrarily late exactly when its cycle is accepting. -/
theorem recurring_target_circuit (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n 1,
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        ∀ a, ∃ t, a ≤ t ∧
          p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      out.size ≤ 80000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size := by
  let f := c.eval Boolean.interpretation
  let P := fun x => p.eval Boolean.interpretation x 0 = true
  obtain ⟨project, hp, hps⟩ := fixed_power n c (Nat.factorial (2 ^ n)) L hL hLN
  obtain ⟨target, ht, hts⟩ := target_reachability c p L hL hLN
  refine ⟨target.comp project, fun x => ?_, ?_⟩
  · rw [Circuit.eval_comp, ht, hp]
    simpa only [cycleProjection, show Fintype.card (State n) = 2 ^ n by simp] using
      (recurring_target_iff f P x).symm
  · have hb : powerBudget n c.size (2 ^ n) L ≤
        powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L := by
      unfold powerBudget
      gcongr
      lia
    simp only [Circuit.size_comp]
    lia

theorem complement_predicate (p : Circuit Boolean.signature n 1) :
    ∃ out : Circuit Boolean.signature n 1,
      (∀ x, out.eval Boolean.interpretation x 0 = !p.eval Boolean.interpretation x 0) ∧
      out.size ≤ p.size + 1 := by
  have hp := Synthesis.circuit (I := Boolean.interpretation) (s := inputs n) p id
    (fun i => ⟨i, rfl⟩)
  have hp' := hp.mono Set.Subset.rfl (show {fun x => p.eval Boolean.interpretation x 0} ⊆
      Set.range (fun j x => p.eval Boolean.interpretation (id x) j) from
    by rintro _ rfl; exact ⟨0, rfl⟩) le_rfl
  obtain ⟨out, ho, hs⟩ := hp'.not.exists_circuit
  exact ⟨out, fun x => congrFun (ho x) 0, hs⟩

/-- A fixed recognizable target eventually holds forever iff rejection does not recur. -/
theorem eventually_always_target_circuit (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n 1,
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        ∃ a, ∀ t, a ≤ t →
          p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      out.size ≤ 80000 * powerBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) L +
        p.size + 2 := by
  classical
  obtain ⟨reject, hr, hrs⟩ := complement_predicate p
  obtain ⟨recurs, hc, hcs⟩ := recurring_target_circuit c reject L hL hLN
  obtain ⟨out, ho, hos⟩ := complement_predicate recurs
  refine ⟨out, fun x => ?_, ?_⟩
  · have hn (b : Bool) : Bool.not b = true ↔ ¬ (b = true) := by cases b <;> decide
    rw [ho, hn, hc]
    simp only [hr, hn, not_forall, not_exists, not_and, not_not]
  · have hb : powerBudget n (c.size + reject.size + 4 * n) (2 ^ n) L ≤
        powerBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) L := by
      unfold powerBudget
      gcongr
    lia

theorem recurring_target_optimized (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) :
    ∃ out : Circuit Boolean.signature n 1,
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        ∀ a, ∃ t, a ≤ t ∧
          p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      (out.size : ℝ) ≤
        240000 * optimizedBudget n (c.size + p.size + 4 * n) (2 ^ n) + p.size := by
  obtain ⟨L, hL, hLN, hopt⟩ :=
    powerBudget_optimized n (c.size + p.size + 4 * n) (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := recurring_target_circuit c p L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤
      80000 * (powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L : ℝ) + p.size := by
    exact_mod_cast hs
  linarith

theorem eventually_always_target_optimized (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) :
    ∃ out : Circuit Boolean.signature n 1,
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        ∃ a, ∀ t, a ≤ t →
          p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      (out.size : ℝ) ≤
        240000 * optimizedBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) + p.size + 2 := by
  obtain ⟨L, hL, hLN, hopt⟩ :=
    powerBudget_optimized n (c.size + (p.size + 1) + 4 * n) (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := eventually_always_target_circuit c p L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤
      80000 * (powerBudget n (c.size + (p.size + 1) + 4 * n) (2 ^ n) L : ℝ) + p.size + 2 := by
    exact_mod_cast hs
  linarith

end IteratedFunctions
