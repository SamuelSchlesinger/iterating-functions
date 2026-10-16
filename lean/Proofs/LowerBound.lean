/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CounterCircuit
public import Proofs.CircuitCounting

/-! # A linear-size permutation with a power requiring exponentially many gates -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

/-- The actual Boolean description budget is smaller than the number of distinct powers. -/
theorem description_budget_lt_period (k : ℕ) (hk : 64 ≤ k) :
    Boolean.signature.orderedBudget (k + k) (k + k) (lowerBudget k) < ModulusCounter.period k := by
  let q := lowerBudget k
  let E := 3 * q + (k + 2) * (2 * q + (k + k) + 1)
  have hb : Boolean.signature.orderedBudget (k + k) (k + k) q ≤ 2 ^ E :=
    boolean_orderedBudget_le_pow _ _ _ _ (lowerBudget_wire_bound k hk)
  have he : E + k < 2 ^ k - 1 := lowerBudget_description_exponent k hk
  have hp : 2 ^ (E + k) < 2 ^ (2 ^ k - 1) := Nat.pow_lt_pow_right (by decide) he
  have hl := Chebyshev.two_pow_le_mul_lcmUpto (2 ^ k - 1)
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.sub_add_cancel hN] at hl
  have hh := (Nat.mul_le_mul_right (2 ^ k) hb).trans_lt
    (by rw [← pow_add]; exact hp)
  have hh' := hh.trans_le hl
  change _ < 2 ^ k * ModulusCounter.period k at hh'
  nlinarith

/-- For every even input width `2k` with `k ≥ 64`, a hard exponent exists below the exact period. -/
theorem exists_hard_counter_power (k : ℕ) (hk : 64 ≤ k) :
    ∃ T < ModulusCounter.period k,
      ∀ out : Circuit Boolean.signature (k + k) (k + k),
        out.Computes Boolean.interpretation (ModulusCounter.power (k := k) T) →
          lowerBudget k < out.size := by
  classical
  let family := Finset.univ.image (fun T : Fin (ModulusCounter.period k) =>
    ModulusCounter.power (k := k) T.val)
  have hcard : family.card = ModulusCounter.period k := by
    rw [Finset.card_image_of_injective _ ModulusCounter.powers_injective]
    simp
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := lowerBudget k)
    Boolean.interpretation family (by rw [hcard]; exact description_budget_lt_period k hk)
  obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨T.val, T.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by lia) hcomp

/-- An end-to-end native-circuit lower bound, including the small update circuit. -/
theorem matching_lower_bound (k : ℕ) (hk : 64 ≤ k) :
    ∃ c : Circuit Boolean.signature (k + k) (k + k),
      c.size ≤ 50 * (k + 1) ∧ Function.Bijective (c.eval Boolean.interpretation) ∧
      ∃ T < ModulusCounter.period k,
        ∀ out : Circuit Boolean.signature (k + k) (k + k),
          out.Computes Boolean.interpretation (c.eval Boolean.interpretation)^[T] →
            2 ^ k / (1024 * (k + 1)) < out.size := by
  obtain ⟨c, hc, hs⟩ := ModulusCounter.exists_linear_circuit k
  obtain ⟨T, hT, hh⟩ := exists_hard_counter_power k hk
  have he : c.eval Boolean.interpretation = ModulusCounter.power (k := k) 1 := funext hc
  refine ⟨c, hs, he ▸ ModulusCounter.power_bijective, T, hT, ?_⟩
  intro out hout
  rw [he, ModulusCounter.iterate_power] at hout
  exact hh out hout

end IteratedFunctions
