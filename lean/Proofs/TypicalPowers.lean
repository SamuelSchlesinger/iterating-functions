/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.LowerBound
import Mathlib.Tactic.Linarith

/-! # Almost every power of the explicit permutation is hard -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

/-- Residues of the exponent whose power has a circuit within the given budget. -/
noncomputable def easyCounterPowers (k q : ℕ) : Finset (Fin (ModulusCounter.period k)) := by
  classical
  exact Finset.univ.filter fun T => ModulusCounter.power (k := k) T.val ∈
    Circuit.functionsAtMost Boolean.interpretation (k + k) (k + k) q

theorem mem_easyCounterPowers (k q : ℕ) (T : Fin (ModulusCounter.period k)) :
    T ∈ easyCounterPowers k q ↔
      ∃ c : Circuit Boolean.signature (k + k) (k + k),
        c.size ≤ q ∧ c.Computes Boolean.interpretation (ModulusCounter.power T.val) := by
  classical
  simp only [easyCounterPowers, Finset.mem_filter, Finset.mem_univ, true_and,
    Circuit.mem_functionsAtMost_iff]
  rfl

theorem easyCounterPowers_card_le (k q : ℕ) :
    (easyCounterPowers k q).card ≤ Boolean.signature.orderedBudget (k + k) (k + k) q := by
  classical
  have hsub : (easyCounterPowers k q).image (fun T => ModulusCounter.power (k := k) T.val) ⊆
      Circuit.functionsAtMost Boolean.interpretation (k + k) (k + k) q := by
    intro target ht
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hT).2
  calc
    _ = ((easyCounterPowers k q).image (fun T => ModulusCounter.power (k := k) T.val)).card :=
      (Finset.card_image_of_injective _ ModulusCounter.powers_injective).symm
    _ ≤ _ := (Finset.card_le_card hsub).trans
      (Circuit.card_functionsAtMost_le Boolean.interpretation)

/-- The description budget leaves an exponential margin in the exponent. -/
theorem lowerBudget_description_margin (k : ℕ) (hk : 64 ≤ k) :
    let q := lowerBudget k
    3 * q + (k + 2) * (2 * q + (k + k) + 1) + k + 2 ^ (k - 1) ≤ 2 ^ k - 1 := by
  dsimp only
  have hq : lowerBudget k * (1024 * (k + 1)) ≤ 2 ^ k := Nat.div_mul_le_self _ _
  have hs := square_le_exponential k hk
  have hpoly : (k + 2) * (k + k + 1) + k + 2 ≤ 4 * (k + 2) ^ 2 := by nlinarith
  have hcoef : (2 * (k + 2) + 3) * 128 ≤ 1024 * (k + 1) := by lia
  have hq' := Nat.mul_le_mul_right (lowerBudget k) hcoef
  have htotal : 128 * (3 * lowerBudget k +
      (k + 2) * (2 * lowerBudget k + (k + k) + 1) + k + 2) ≤ 5 * 2 ^ k := by
    nlinarith
  have hhalf : 2 ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (by lia : 1 ≤ k)]
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  lia

/-- Exact counting form: the easy fraction is at most `2^(-2^(k-1))`.
This counts exponents uniformly modulo the full period, without restricting
the bit length of their descriptions. -/
theorem almost_every_counter_power (k : ℕ) (hk : 64 ≤ k) :
    (easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1)) ≤
      ModulusCounter.period k := by
  let E := 3 * lowerBudget k + (k + 2) * (2 * lowerBudget k + (k + k) + 1)
  have heasy : (easyCounterPowers k (lowerBudget k)).card ≤ 2 ^ E :=
    (easyCounterPowers_card_le k _).trans
      (boolean_orderedBudget_le_pow _ _ _ _ (lowerBudget_wire_bound k hk))
  have he : E + 2 ^ (k - 1) + k ≤ 2 ^ k - 1 := by
    have := lowerBudget_description_margin k hk
    dsimp only at this
    dsimp [E]
    lia
  have hl := Chebyshev.two_pow_le_mul_lcmUpto (2 ^ k - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := k))] at hl
  have hscaled : ((easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1))) * 2 ^ k ≤
      ModulusCounter.period k * 2 ^ k := by
    calc
      _ ≤ (2 ^ E * 2 ^ (2 ^ (k - 1))) * 2 ^ k := by gcongr
      _ = 2 ^ (E + 2 ^ (k - 1) + k) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (2 ^ k - 1) := Nat.pow_le_pow_right (by decide) he
      _ ≤ _ := by simpa only [ModulusCounter.period, Nat.mul_comm] using hl
  exact Nat.le_of_mul_le_mul_right hscaled (by positivity)

end IteratedFunctions
