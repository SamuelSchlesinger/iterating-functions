/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Extensions
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! # Permutation inversion and cyclicity

Factorial exponents avoid computing a permutation's order. Their numerical
size has no effect on the fixed-power gate bound.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

universe u
variable {α : Type u} [Fintype α] {n : ℕ}

theorem iterate_factorial_pred_eq_symm (p : Equiv.Perm α) :
    (p : α → α)^[Nat.factorial (Fintype.card α) - 1] = p.symm := by
  funext x
  have h := congrFun (Function.injective_iff_iterate_factorial_card_eq_id.mp
    p.injective) (p.symm x)
  have hpos := Nat.factorial_pos (Fintype.card α)
  conv_rhs at h => change p.symm x
  rw [show Nat.factorial (Fintype.card α) = (Nat.factorial (Fintype.card α) - 1) + 1 by lia,
    Function.iterate_succ_apply, p.apply_symm_apply] at h
  exact h

/-- Exact inversion, with no cost depending on the factorial exponent. -/
theorem permutation_inverse (c : Circuit Boolean.signature n n) (p : Equiv.Perm (State n))
    (hc : c.Computes Boolean.interpretation p) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation p.symm ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L := by
  obtain ⟨out, hout, hs⟩ := fixed_power n c (Nat.factorial (Fintype.card (State n)) - 1) L hL hLN
  have he : c.eval Boolean.interpretation = p := funext hc
  exact ⟨out, by simpa only [he, iterate_factorial_pred_eq_symm] using hout, hs⟩

/-- Inversion on an arbitrary finite state type, using its supplied bit encoding. -/
theorem permutation_inverse_encoded (p : Equiv.Perm α) (e : α → State n)
    (he : Function.Injective e) (c : Circuit Boolean.signature n n)
    (hc : ∀ x, c.eval Boolean.interpretation (e x) = e (p x))
    (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      (∀ x, out.eval Boolean.interpretation (e x) = e (p.symm x)) ∧
      out.size ≤ 40000 * powerBudget n c.size (Fintype.card α) L := by
  obtain ⟨out, hout, hs⟩ := fixed_power_encoded p Finset.univ e he.injOn c
    (fun _ _ => Finset.mem_univ _) (fun x _ => hc x)
    (Nat.factorial (Fintype.card α) - 1) L hL hLN
  refine ⟨out, fun x => ?_, by simpa using hs⟩
  simpa only [iterate_factorial_pred_eq_symm] using hout x (Finset.mem_univ x)

/-- Cyclicity is an equality test against one fixed iterate. -/
theorem cyclicity_circuit (c : Circuit Boolean.signature n n)
    (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n 1,
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        x ∈ Function.periodicPts (c.eval Boolean.interpretation)) ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L + (6 * n + 1) := by
  classical
  let f := c.eval Boolean.interpretation
  let T := Nat.factorial (Fintype.card (State n))
  obtain ⟨pow, hp, hs⟩ := fixed_power n c T L hL hLN
  have hpow := Synthesis.circuit (I := Boolean.interpretation) (s := inputs n) pow id
    (fun bit => ⟨bit, rfl⟩)
  have heq := synthesis_bits_eq (inputs n ∪ wires (pow.eval Boolean.interpretation))
    (pow.eval Boolean.interpretation) id (fun _ h => Or.inr h) (fun _ h => Or.inl h)
  obtain ⟨out, hout, hsize⟩ := (hpow.trans heq).exists_circuit
  refine ⟨out, fun x => ?_, hsize.trans (Nat.add_le_add_right hs _)⟩
  rw [hout x]
  change decide (pow.eval Boolean.interpretation x = x) = true ↔ _
  rw [decide_eq_true_eq, hp x]
  exact (Function.mem_periodicPts_iff_isPeriodicPt_factorial_card).symm

end IteratedFunctions
