/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.OrbitStructure
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.ModEq

/-! # Canonical cycles and coordinates, independent of a Boolean representation -/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Finite α] (f : α → α)

omit [Finite α] in
/-- Periodic points reached at different times along one trajectory have the same period. -/
theorem minimalPeriod_eq_of_periodic_iterates (x : α) {a b : ℕ}
    (ha : f^[a] x ∈ Function.periodicPts f) (hb : f^[b] x ∈ Function.periodicPts f) :
    Function.minimalPeriod f (f^[a] x) = Function.minimalPeriod f (f^[b] x) := by
  rcases le_total a b with h | h
  · have ht : f^[b] x = f^[b - a] (f^[a] x) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, Function.minimalPeriod_apply_iterate ha]
  · have ht : f^[a] x = f^[a - b] (f^[b] x) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, Function.minimalPeriod_apply_iterate hb]

theorem cycleLength_iterate (x : α) (t : ℕ) : cycleLength f (f^[t] x) = cycleLength f x := by
  unfold cycleLength
  rw [← Function.iterate_add_apply]
  apply minimalPeriod_eq_of_periodic_iterates
  · rw [Function.iterate_add_apply]
    exact transientDepth_spec f _
  · exact transientDepth_spec f x

theorem minimalPeriod_at_periodic_iterate (x : α) {t : ℕ}
    (ht : f^[t] x ∈ Function.periodicPts f) :
    Function.minimalPeriod f (f^[t] x) = cycleLength f x :=
  minimalPeriod_eq_of_periodic_iterates f x ht (transientDepth_spec f x)

/-- Repetition in a short prefix bounds both the depth and the eventual cycle length. -/
theorem depth_add_cycleLength_le_repeat (x : α) {i j : ℕ}
    (hij : i < j) (he : f^[i] x = f^[j] x) : transientDepth f x + cycleLength f x ≤ j := by
  have hp := Function.mk_mem_periodicPts (by lia : 0 < j - i) (periodic_of_repeat hij.le he)
  have hm := Function.IsPeriodicPt.minimalPeriod_le (by lia : 0 < j - i)
    (periodic_of_repeat hij.le he)
  rw [minimalPeriod_at_periodic_iterate f x hp] at hm
  have hd := (periodic_iterate_iff f x i).mp hp
  lia

noncomputable def cycleSet (x : α) : Finset α := by
  classical
  exact Finset.univ.image fun j : Fin (cycleLength f x) =>
    f^[j.val] (f^[transientDepth f x] x)

theorem mem_cycleSet_iff (x y : α) :
    y ∈ cycleSet f x ↔ y ∈ Function.periodicOrbit f (f^[transientDepth f x] x) := by
  classical
  rw [Function.mem_periodicOrbit_iff (transientDepth_spec f x)]
  simp only [cycleSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j.val, hj⟩
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t % cycleLength f x, Nat.mod_lt _ (cycleLength_pos f x)⟩,
      (cycleLength_periodic f x).iterate_mod_apply t⟩

theorem cycleSet_nonempty (x : α) : (cycleSet f x).Nonempty := by
  classical
  exact ⟨_, (mem_cycleSet_iff f x _).mpr
    (Function.self_mem_periodicOrbit (transientDepth_spec f x))⟩

theorem cycleSet_iterate (x : α) (t : ℕ) : cycleSet f (f^[t] x) = cycleSet f x := by
  classical
  ext y
  rw [mem_cycleSet_iff, mem_cycleSet_iff, ← Function.iterate_add_apply]
  let a := transientDepth f (f^[t] x) + t
  let b := transientDepth f x
  have ha : f^[a] x ∈ Function.periodicPts f := by
    dsimp [a]
    rw [Function.iterate_add_apply]
    exact transientDepth_spec f _
  have hb : f^[b] x ∈ Function.periodicPts f := transientDepth_spec f x
  change y ∈ Function.periodicOrbit f (f^[a] x) ↔ y ∈ Function.periodicOrbit f (f^[b] x)
  rcases le_total a b with h | h
  · have ht : f^[b] x = f^[b - a] (f^[a] x) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, Function.periodicOrbit_apply_iterate_eq ha]
  · have ht : f^[a] x = f^[a - b] (f^[b] x) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]
    rw [ht, Function.periodicOrbit_apply_iterate_eq hb]

theorem cycleSet_spec {x y : α} (hy : y ∈ cycleSet f x) :
    y ∈ Function.periodicPts f ∧ ∃ t, f^[t] x = y := by
  classical
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  constructor
  · obtain ⟨p, hp, hper⟩ := Function.mem_periodicPts.mp (transientDepth_spec f x)
    exact Function.mk_mem_periodicPts hp (hper.apply_iterate j.val)
  · exact ⟨j.val + transientDepth f x, Function.iterate_add_apply _ _ _ _⟩

variable [LinearOrder α]

/-- The least element of the eventual cycle in the chosen state order. -/
noncomputable def canonicalCycle (x : α) : α := (cycleSet f x).min' (cycleSet_nonempty f x)

theorem canonicalCycle_mem (x : α) : canonicalCycle f x ∈ cycleSet f x :=
  Finset.min'_mem _ _

theorem canonicalCycle_le (x : α) {y : α} (hy : y ∈ cycleSet f x) : canonicalCycle f x ≤ y :=
  Finset.min'_le _ _ hy

theorem canonicalCycle_iterate (x : α) (t : ℕ) :
    canonicalCycle f (f^[t] x) = canonicalCycle f x := by
  unfold canonicalCycle
  simp only [cycleSet_iterate]

theorem canonicalCycle_periodic (x : α) : canonicalCycle f x ∈ Function.periodicPts f :=
  (cycleSet_spec f (canonicalCycle_mem f x)).1

theorem canonicalCycle_reachable (x : α) : ∃ t, f^[t] x = canonicalCycle f x :=
  (cycleSet_spec f (canonicalCycle_mem f x)).2

/-- A canonical representative completely identifies the eventual cycle. -/
theorem cyclic_reachable_iff (x y : α) (hy : y ∈ Function.periodicPts f) :
    (∃ t, f^[t] x = y) ↔ canonicalCycle f x = canonicalCycle f y := by
  constructor
  · rintro ⟨t, rfl⟩
    exact (canonicalCycle_iterate f x t).symm
  · intro he
    obtain ⟨a, ha⟩ := canonicalCycle_reachable f x
    obtain ⟨b, hb⟩ := canonicalCycle_reachable f y
    have hp := Function.isPeriodicPt_minimalPeriod f y
    let d := Function.minimalPeriod f y
    have hd : 0 < d := Function.minimalPeriod_pos_of_mem_periodicPts hy
    have hback : f^[d - b % d] (canonicalCycle f y) = y := by
      rw [← hb, ← hp.iterate_mod_apply b, ← Function.iterate_add_apply,
        Nat.sub_add_cancel (Nat.mod_lt b hd).le]
      exact hp
    refine ⟨(d - b % d) + a, ?_⟩
    rw [Function.iterate_add_apply, ha, he]
    exact hback

/-- The first visit to the canonical cycle representative, always below the state count. -/
noncomputable def canonicalTime (x : α) : ℕ := Nat.find (canonicalCycle_reachable f x)

theorem canonicalTime_spec (x : α) : f^[canonicalTime f x] x = canonicalCycle f x :=
  Nat.find_spec (canonicalCycle_reachable f x)

theorem canonicalTime_min (x : α) {j : ℕ} (hj : j < canonicalTime f x) :
    f^[j] x ≠ canonicalCycle f x := Nat.find_min (canonicalCycle_reachable f x) hj

theorem canonicalTime_lt_cycleLength (x : α) (hx : x ∈ Function.periodicPts f) :
    canonicalTime f x < cycleLength f x := by
  have hp : Function.IsPeriodicPt f (cycleLength f x) x := by
    simpa only [(transientDepth_eq_zero_iff f x).mpr hx, Function.iterate_zero_apply]
      using cycleLength_periodic f x
  have ht := (hp.iterate_mod_apply (canonicalTime f x)).trans (canonicalTime_spec f x)
  exact (Nat.find_min' (canonicalCycle_reachable f x) ht).trans_lt
    (Nat.mod_lt _ (cycleLength_pos f x))

theorem canonicalTime_lt_card [Fintype α] (x : α) : canonicalTime f x < Fintype.card α := by
  obtain ⟨t, ht, hp, _⟩ := exists_first_visit f (fun y => y = canonicalCycle f x) x
    (canonicalCycle_reachable f x)
  exact (Nat.find_min' (canonicalCycle_reachable f x) hp).trans_lt ht

/-- A natural-number encoding of phase: the negative of the canonical hitting time modulo `ℓ`. -/
noncomputable def phase (x : α) : ℕ :=
  (cycleLength f x - canonicalTime f x % cycleLength f x) % cycleLength f x

theorem phase_lt (x : α) : phase f x < cycleLength f x := Nat.mod_lt _ (cycleLength_pos f x)

end IteratedFunctions
