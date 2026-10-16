/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.VisitSchedules
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith

/-! # Counting visits from a schedule, including singleton schedules -/

@[expose] public section

namespace IteratedFunctions

def arithmeticProgressionCount (d p T : ℕ) : ℕ :=
  if T < d then 0 else if p = 0 then 1 else (T - d) / p + 1

theorem arithmeticProgressionCount_spec (d p T : ℕ) :
    Set.ncard {t : ℕ | t ≤ T ∧ ∃ k, t = d + k * p} =
      arithmeticProgressionCount d p T := by
  classical
  have hset : {t : ℕ | t ≤ T ∧ ∃ k, t = d + k * p} =
      ↑((Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
      Nat.lt_succ_iff]
  rw [hset, Set.ncard_coe_finset]
  unfold arithmeticProgressionCount
  split_ifs with hT hp
  · have he : (Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ht, k, rfl⟩ := Finset.mem_filter.mp ht
      have hlt := Finset.mem_range.mp ht
      lia
    rw [he, Finset.card_empty]
  · have he : (Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p) = {d} := by
      ext t
      simp only [hp, Nat.mul_zero, Nat.add_zero, exists_const, Finset.mem_filter,
        Finset.mem_range, Finset.mem_singleton]
      lia
    rw [he, Finset.card_singleton]
  · have hpos : 0 < p := by lia
    have he : (Finset.range (T + 1)).filter (fun t => ∃ k, t = d + k * p) =
        (Finset.range ((T - d) / p + 1)).image (fun k => d + k * p) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨ht, k, rfl⟩
        refine ⟨k, ?_, rfl⟩
        have hh : k ≤ (T - d) / p := (Nat.le_div_iff_mul_le hpos).mpr (by lia)
        lia
      · rintro ⟨k, hk, rfl⟩
        have hh : k * p ≤ T - d :=
          (Nat.le_div_iff_mul_le hpos).mp (show k ≤ (T - d) / p by lia)
        exact ⟨by lia, k, rfl⟩
    rw [he, Finset.card_image_of_injective _ (show Function.Injective
      (fun k : ℕ => d + k * p) from by intro a b hab; nlinarith), Finset.card_range]

universe u
variable {α : Type u}

theorem visit_count_of_first (f : α → α) (x y : α) (d : ℕ)
    (hd : f^[d] x = y) (hfirst : ∀ j < d, f^[j] x ≠ y) (T : ℕ) :
    Set.ncard {t : ℕ | t ≤ T ∧ f^[t] x = y} =
      arithmeticProgressionCount d (Function.minimalPeriod f y) T := by
  classical
  have he : {t : ℕ | t ≤ T ∧ f^[t] x = y} =
      {t : ℕ | t ≤ T ∧ ∃ k, t = d + k * Function.minimalPeriod f y} := by
    ext t
    simp only [Set.mem_ofPred_eq, visit_schedule_of_first f x y d hd hfirst t]
  rw [he, arithmeticProgressionCount_spec]

end IteratedFunctions
