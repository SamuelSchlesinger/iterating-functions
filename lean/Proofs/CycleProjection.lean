/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.HittingTimes

/-!
# Cycle projection and eventual queries

A factorial iterate retracts a finite dynamical system onto its cyclic states.
All statements are universe polymorphic. No order on the state type is needed.
-/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Fintype α] (f : α → α)

def cycleProjection (x : α) : α := f^[(Nat.factorial (Fintype.card α))] x

theorem iterate_card_periodic (x : α) :
    f^[Fintype.card α] x ∈ Function.periodicPts f :=
  (periodic_iterate_iff f x _).mpr (transientDepth_lt_card f x).le

theorem cycleProjection_periodic (x : α) : cycleProjection f x ∈ Function.periodicPts f :=
  (periodic_iterate_iff f x _).mpr
    ((transientDepth_lt_card f x).le.trans (Nat.self_le_factorial _))

theorem cycleProjection_fixed_iff (x : α) :
    cycleProjection f x = x ↔ x ∈ Function.periodicPts f :=
  Function.mem_periodicPts_iff_isPeriodicPt_factorial_card.symm

@[simp] theorem cycleProjection_idempotent (x : α) :
    cycleProjection f (cycleProjection f x) = cycleProjection f x :=
  (cycleProjection_fixed_iff f _).mpr (cycleProjection_periodic f x)

theorem cycleProjection_iterate (x : α) (t : ℕ) :
    cycleProjection f (f^[t] x) = f^[t] (cycleProjection f x) := by
  unfold cycleProjection
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

/-- The original orbit agrees with its projected orbit exactly from cycle entry onward. -/
theorem iterate_eq_projection_iff (x : α) (t : ℕ) :
    f^[t] x = f^[t] (cycleProjection f x) ↔ transientDepth f x ≤ t := by
  rw [← cycleProjection_iterate, eq_comm, cycleProjection_fixed_iff, periodic_iterate_iff]

omit [Fintype α] in
/-- Equal future positions of two cyclic states imply equal starting positions. -/
theorem periodic_iterate_inj {x y : α} (hx : x ∈ Function.periodicPts f)
    (hy : y ∈ Function.periodicPts f) (t : ℕ) (he : f^[t] x = f^[t] y) : x = y :=
  ((Function.bijOn_periodicPts f).iterate t).injOn hx hy he

/-- Synchronous coalescence, unlike orbit intersection, is tested at one fixed time. -/
theorem eventual_coalescence_iff (x y : α) :
    (∃ t, f^[t] x = f^[t] y) ↔ f^[Fintype.card α] x = f^[Fintype.card α] y := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases hle : t ≤ Fintype.card α
    · have h := congrArg (f^[Fintype.card α - t]) ht
      simpa only [← Function.iterate_add_apply, Nat.sub_add_cancel hle] using h
    · apply periodic_iterate_inj f (iterate_card_periodic f x) (iterate_card_periodic f y)
        (t - Fintype.card α)
      simpa only [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia :
        Fintype.card α ≤ t)] using ht
  · exact fun h => ⟨_, h⟩

/-- A bounded representative of every input time, even when its description is very long. -/
noncomputable def normalizedTime (x : α) (t : ℕ) : ℕ :=
  if t < Fintype.card α then t else
    Fintype.card α + (t - Fintype.card α) % cycleLength f x

theorem normalizedTime_lt (x : α) (t : ℕ) : normalizedTime f x t < 2 * Fintype.card α := by
  unfold normalizedTime
  split_ifs with ht
  · lia
  · have hp := Nat.mod_lt (t - Fintype.card α) (cycleLength_pos f x)
    have hc := depth_add_cycleLength_le_card f x
    lia

theorem iterate_normalizedTime (x : α) (t : ℕ) :
    f^[normalizedTime f x t] x = f^[t] x := by
  unfold normalizedTime
  split_ifs with ht
  · rfl
  · apply (iterate_eq_iff_modEq_after f x
      (by have := transientDepth_lt_card f x; lia)
      (by have := transientDepth_lt_card f x; lia)).mpr
    unfold Nat.ModEq
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_sub_of_le (by lia : Fintype.card α ≤ t)]

/-- Recurrence is equivalent to one successful future visit from the cycle projection. -/
theorem recurring_target_iff (P : α → Prop) (x : α) :
    (∀ a, ∃ t, a ≤ t ∧ P (f^[t] x)) ↔ ∃ t, P (f^[t] (cycleProjection f x)) := by
  constructor
  · intro h
    obtain ⟨t, ht, hp⟩ := h (Nat.factorial (Fintype.card α))
    refine ⟨t - (Nat.factorial (Fintype.card α)), ?_⟩
    simpa only [cycleProjection, ← Function.iterate_add_apply, Nat.sub_add_cancel ht] using hp
  · rintro ⟨t, ht⟩ a
    obtain ⟨p, hp, hperiod⟩ := Function.mem_periodicPts.mp (cycleProjection_periodic f x)
    refine ⟨a * p + t + (Nat.factorial (Fintype.card α)), ?_, ?_⟩
    · have := Nat.mul_le_mul_left a hp
      lia
    · have he : f^[a * p + t + (Nat.factorial (Fintype.card α))] x =
          f^[t] (cycleProjection f x) := by
        rw [Function.iterate_add_apply, Function.iterate_add_apply]
        exact (hperiod.apply_iterate t).const_mul a
      rwa [he]

/-- Eventual permanent acceptance is the absence of a rejected state on the eventual cycle. -/
theorem eventually_always_target_iff (P : α → Prop) (x : α) :
    (∃ a, ∀ t, a ≤ t → P (f^[t] x)) ↔
      ¬ ∃ t, ¬ P (f^[t] (cycleProjection f x)) := by
  classical
  rw [← recurring_target_iff f (fun y => ¬ P y) x]
  simp only [not_forall, not_exists, not_and, not_not]

end IteratedFunctions
