/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.FiniteOrbit

/-! # Transient depth and exact eventual period on arbitrary finite state types -/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Finite α] (f : α → α)

theorem exists_periodic_iterate (x : α) : ∃ t, f^[t] x ∈ Function.periodicPts f := by
  classical
  let _ := Fintype.ofFinite α
  have hn : ¬ Function.Injective (fun i : Fin (Fintype.card α + 1) => f^[i.val] x) := by
    intro h
    have hc := Fintype.card_le_of_injective _ h
    simp only [Fintype.card_fin] at hc
    lia
  obtain ⟨i, j, he, hne⟩ := Function.not_injective_iff.mp hn
  have helper (i j : ℕ) (hij : i < j) (he : f^[i] x = f^[j] x) :
      ∃ t, f^[t] x ∈ Function.periodicPts f :=
    ⟨i, Function.mk_mem_periodicPts (by lia : 0 < j - i) (periodic_of_repeat hij.le he)⟩
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact helper i j hij he
  · exact helper j i hji he.symm

noncomputable def transientDepth (x : α) : ℕ := by
  classical
  exact Nat.find (exists_periodic_iterate f x)

theorem transientDepth_spec (x : α) :
    f^[transientDepth f x] x ∈ Function.periodicPts f := by
  classical
  exact Nat.find_spec (exists_periodic_iterate f x)

theorem transientDepth_min (x : α) {t : ℕ} (ht : t < transientDepth f x) :
    f^[t] x ∉ Function.periodicPts f := by
  classical
  exact Nat.find_min (exists_periodic_iterate f x) ht

theorem transientDepth_lt_card [Fintype α] (x : α) :
    transientDepth f x < Fintype.card α := by
  classical
  obtain ⟨t, ht, hp, _⟩ := exists_first_visit f (fun y => y ∈ Function.periodicPts f) x
    (exists_periodic_iterate f x)
  exact (Nat.find_min' (exists_periodic_iterate f x) hp).trans_lt ht

theorem periodic_iterate_iff (x : α) (t : ℕ) :
    f^[t] x ∈ Function.periodicPts f ↔ transientDepth f x ≤ t := by
  classical
  constructor
  · exact Nat.find_min' (exists_periodic_iterate f x)
  · intro ht
    obtain ⟨p, hp, hperiod⟩ := Function.mem_periodicPts.mp (transientDepth_spec f x)
    have h := Function.mk_mem_periodicPts hp (hperiod.apply_iterate (t - transientDepth f x))
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel ht] at h

@[simp] theorem transientDepth_eq_zero_iff (x : α) :
    transientDepth f x = 0 ↔ x ∈ Function.periodicPts f := by
  simpa using (periodic_iterate_iff f x 0).symm

theorem transientDepth_iterate (x : α) (t : ℕ) :
    transientDepth f (f^[t] x) = transientDepth f x - t := by
  apply Nat.le_antisymm
  · apply (periodic_iterate_iff f (f^[t] x) _).mp
    rw [← Function.iterate_add_apply, periodic_iterate_iff]
    lia
  · have h := transientDepth_spec f (f^[t] x)
    rw [← Function.iterate_add_apply, periodic_iterate_iff] at h
    lia

noncomputable def cycleLength (x : α) : ℕ :=
  Function.minimalPeriod f (f^[transientDepth f x] x)

theorem cycleLength_pos (x : α) : 0 < cycleLength f x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (transientDepth_spec f x)

theorem cycleLength_periodic (x : α) :
    Function.IsPeriodicPt f (cycleLength f x) (f^[transientDepth f x] x) :=
  Function.isPeriodicPt_minimalPeriod _ _

/-- The transient and one complete cycle contain no repeated states. -/
theorem orbit_prefix_injective (x : α) :
    Function.Injective (fun i : Fin (transientDepth f x + cycleLength f x) => f^[i.val] x) := by
  intro i j he
  apply Fin.ext
  by_contra hne
  have bad (a b : ℕ) (hab : a < b) (hb : b < transientDepth f x + cycleLength f x)
      (he : f^[a] x = f^[b] x) : False := by
    have hp : f^[a] x ∈ Function.periodicPts f :=
      Function.mk_mem_periodicPts (by lia : 0 < b - a) (periodic_of_repeat hab.le he)
    have ha := (periodic_iterate_iff f x a).mp hp
    have he' : f^[a - transientDepth f x] (f^[transientDepth f x] x) =
        f^[b - transientDepth f x] (f^[transientDepth f x] x) := by
      simpa only [← Function.iterate_add_apply, Nat.sub_add_cancel ha,
        Nat.sub_add_cancel (ha.trans hab.le)] using he
    have hh := Function.iterate_injOn_Iio_minimalPeriod
      (show a - transientDepth f x < cycleLength f x by lia)
      (show b - transientDepth f x < cycleLength f x by lia) he'
    lia
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact bad i.val j.val hij j.isLt he
  · exact bad j.val i.val hji i.isLt he.symm

theorem depth_add_cycleLength_le_card [Fintype α] (x : α) :
    transientDepth f x + cycleLength f x ≤ Fintype.card α := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (orbit_prefix_injective f x)

/-- A transient target can only occur at the difference of transient depths. -/
theorem transient_reachable_iff (x y : α) (hy : y ∉ Function.periodicPts f) :
    (∃ t, f^[t] x = y) ↔
      transientDepth f y ≤ transientDepth f x ∧
        f^[transientDepth f x - transientDepth f y] x = y := by
  have hypos : 0 < transientDepth f y := by
    have := (transientDepth_eq_zero_iff f y).not.mpr hy
    lia
  constructor
  · rintro ⟨t, rfl⟩
    rw [transientDepth_iterate] at hypos ⊢
    have ht : t < transientDepth f x := by lia
    exact ⟨Nat.sub_le _ _, by congr 1; lia⟩
  · rintro ⟨_, ht⟩
    exact ⟨_, ht⟩

end IteratedFunctions
