/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Navigation

/-!
# Complete schedules of visits

After the first visit to a target, subsequent visits form an arithmetic
progression. The convention of period zero for a nonperiodic target makes
a single visit a special case of the same formula. This semantic fact does
not require a finite state space.
-/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u}

theorem visit_schedule_of_first (f : α → α) (x y : α) (d : ℕ)
    (hd : f^[d] x = y) (hfirst : ∀ j < d, f^[j] x ≠ y) (t : ℕ) :
    f^[t] x = y ↔ ∃ k, t = d + k * Function.minimalPeriod f y := by
  constructor
  · intro ht
    have hle : d ≤ t := by by_contra h; exact hfirst t (by lia) ht
    have hp : Function.IsPeriodicPt f (t - d) y := by
      change f^[t - d] y = y
      rw [← hd, ← Function.iterate_add_apply, Nat.sub_add_cancel hle]
      exact ht.trans hd.symm
    obtain ⟨k, hk⟩ := Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hp
    exact ⟨k, by rw [Nat.mul_comm] at hk; lia⟩
  · rintro ⟨k, rfl⟩
    rw [Nat.add_comm, Function.iterate_add_apply, hd]
    exact (Function.isPeriodicPt_minimalPeriod f y).const_mul k

theorem visit_before_deadline_of_first (f : α → α) (x y : α) (d : ℕ)
    (hd : f^[d] x = y) (hfirst : ∀ j < d, f^[j] x ≠ y) (T : ℕ) :
    (∃ t ≤ T, f^[t] x = y) ↔ d ≤ T := by
  constructor
  · rintro ⟨t, ht, hy⟩
    obtain ⟨k, rfl⟩ := (visit_schedule_of_first f x y d hd hfirst t).mp hy
    lia
  · exact fun h => ⟨d, h, hd⟩

variable [Fintype α] [LinearOrder α]

theorem visit_schedule (f : α → α) (x y : α) (t : ℕ) :
    f^[t] x = y ↔ reaches f x y = true ∧
      ∃ k, t = hittingTime f x y + k * Function.minimalPeriod f y := by
  constructor
  · intro ht
    have hr := (reaches_iff f x y).mpr ⟨t, ht⟩
    have hd := hittingTime_spec f x y hr
    exact ⟨hr, (visit_schedule_of_first f x y _ hd.1 hd.2.1 t).mp ht⟩
  · rintro ⟨hr, ht⟩
    have hd := hittingTime_spec f x y hr
    exact (visit_schedule_of_first f x y _ hd.1 hd.2.1 t).mpr ht

end IteratedFunctions
