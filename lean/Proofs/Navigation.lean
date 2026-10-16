/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.HittingTimes
public import Proofs.FiniteOrbit

/-! # Reachability and exact first hitting times on arbitrary finite types -/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Fintype α] [LinearOrder α] (f : α → α)

noncomputable def reaches (x y : α) : Bool :=
  if transientDepth f y = 0 then decide (canonicalCycle f x = canonicalCycle f y)
  else decide (transientDepth f y ≤ transientDepth f x) &&
    decide (f^[transientDepth f x - transientDepth f y] x = y)

noncomputable def hittingTime (x y : α) : ℕ :=
  if transientDepth f y = 0 then transientDepth f x + cyclicDistance f x y
  else transientDepth f x - transientDepth f y

theorem reaches_iff (x y : α) : reaches f x y = true ↔ ∃ t, f^[t] x = y := by
  unfold reaches
  split_ifs with hy
  · rw [decide_eq_true_eq]
    exact (cyclic_reachable_iff f x y ((transientDepth_eq_zero_iff f y).mp hy)).symm
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact (transient_reachable_iff f x y (by
      intro h; exact hy ((transientDepth_eq_zero_iff f y).mpr h))).symm

/-- The candidate time is specified only when the target is reachable. -/
theorem hittingTime_spec (x y : α) (h : reaches f x y = true) :
    f^[hittingTime f x y] x = y ∧
      (∀ j < hittingTime f x y, f^[j] x ≠ y) ∧
      hittingTime f x y < Fintype.card α := by
  have hr := (reaches_iff f x y).mp h
  have hfirst : f^[hittingTime f x y] x = y ∧
      ∀ j < hittingTime f x y, f^[j] x ≠ y := by
    unfold hittingTime
    split_ifs with hy
    · have hp := (transientDepth_eq_zero_iff f y).mp hy
      exact cyclic_first_hit f x y hp ((cyclic_reachable_iff f x y hp).mp hr)
    · have hp : y ∉ Function.periodicPts f := fun hp =>
        hy ((transientDepth_eq_zero_iff f y).mpr hp)
      obtain ⟨hle, he⟩ := (transient_reachable_iff f x y hp).mp hr
      refine ⟨he, fun j hj hjy => ?_⟩
      have hd := transientDepth_iterate f x j
      rw [hjy] at hd
      have hpos : 0 < transientDepth f y := Nat.pos_of_ne_zero hy
      lia
  obtain ⟨t, ht, hty, hmin⟩ := exists_first_visit f (fun z => z = y) x hr
  have he : t = hittingTime f x y := by
    apply Nat.le_antisymm
    · by_contra hle
      exact hmin _ (by lia) hfirst.1
    · by_contra hle
      exact hfirst.2 _ (by lia) hty
  exact ⟨hfirst.1, hfirst.2, he ▸ ht⟩

end IteratedFunctions
