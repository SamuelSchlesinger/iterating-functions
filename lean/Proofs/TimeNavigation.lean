/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ForestNavigation
public import Proofs.HittingTimes

/-!
# Iterates of a queried length through a compressed checkpoint forest

Depth and ancestry intervals locate a transient target, and phases locate a
cyclic one. In both cases an arbitrary marked vertex passing a short-distance
filter suffices: no minimum over marks and no binary powering is required.
-/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Finite α] (f : α → α) (H : Finset α) (L : ℕ)

/-- Every mark passing the transient filter walks to the requested iterate. -/
theorem forest_ancestor_walk (low high : α → Fin (Nat.card α))
    (hinterval : ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y)
    {x h a : α} {d t : ℕ} (hd : f^[d] x = h) (hdt : d ≤ t) (ht : t < transientDepth f x)
    (hlow : low a ≤ low h) (hhigh : low h ≤ high a)
    (hdepth : transientDepth f x - t ≤ transientDepth f a) :
    f^[transientDepth f a - (transientDepth f x - t)] a = f^[t] x := by
  obtain ⟨e, he, hea⟩ := (hinterval h a).mp ⟨hlow, hhigh⟩
  have hh := transientDepth_iterate f x d
  rw [hd] at hh
  have ha := transientDepth_iterate f h e
  rw [hea] at ha
  have hw : transientDepth f a - (transientDepth f x - t) + e + d = t := by lia
  conv_rhs => rw [← hw]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, hd, hea]

/-- Some mark passes the transient filter once a prefix contains a mark. -/
theorem exists_forest_ancestor_mark (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    (low high : α → Fin (Nat.card α))
    (hinterval : ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y)
    {x h : α} {d t : ℕ} (hh : h ∈ forestMarks f H) (hd : f^[d] x = h) (hdt : d ≤ t)
    (ht : t < transientDepth f x) :
    ∃ a ∈ forestMarks f H, low a ≤ low h ∧ low h ≤ high a ∧
      transientDepth f x - t ≤ transientDepth f a ∧
      transientDepth f a - (transientDepth f x - t) ≤ 2 * L := by
  have hy : transientDepth f (f^[t] x) = transientDepth f x - t := transientDepth_iterate f x t
  have hpos : 0 < transientDepth f (f^[t] x) := by lia
  have hreach : ∃ e, f^[e] h = f^[t] x := by
    refine ⟨t - d, ?_⟩
    rw [← hd, ← Function.iterate_add_apply, Nat.sub_add_cancel hdt]
  have hyS := forest_transient_reachable_mem f H (forestMarks_subset_hull f H hh) hpos hreach
  obtain ⟨a, ha⟩ := exists_forest_anchor f H L hL hcover hyS
  obtain ⟨hmem, ⟨i, hi, hiy⟩, hthrough⟩ := forest_anchor_contains f H L hyS ha
  obtain ⟨e, he⟩ := hthrough h hh hreach
  have hai := transientDepth_iterate f a i
  rw [hiy] at hai
  have hhe := transientDepth_iterate f h e
  rw [he] at hhe
  have hinter := (hinterval h a).mpr ⟨e, by lia, he⟩
  exact ⟨a, hmem, hinter.1, hinter.2, by lia, by lia⟩

/-- A transient target beyond the prefix guarantees a checkpoint in the prefix. -/
theorem exists_prefix_checkpoint
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {x : α} {t : ℕ} (hK : 2 * L < t) (ht : t < transientDepth f x) :
    ∃ d < 2 * L, f^[d] x ∈ H := by
  have hy := transientDepth_iterate f x t
  obtain ⟨d, hd, hmem, _⟩ := checkpoint_before_distant_target f H hcover
    (x := x) (y := f^[t] x) (by lia) ⟨t, rfl⟩ (fun i hi he => by
      have hh := transientDepth_iterate f x i
      rw [he] at hh
      lia)
  exact ⟨d, hd, hmem⟩

variable [LinearOrder α]

/-- Every cyclic mark at a phase below the target walks forward to it. -/
theorem cycle_mark_walk {a c : α} (ha : a ∈ Function.periodicPts f)
    (hc : canonicalCycle f a = c) {p : ℕ} (hp : phase f a ≤ p) :
    f^[p - phase f a] a = f^[p] c := by
  have hs := phase_spec f a (t := 0)
    (by simp [(transientDepth_eq_zero_iff f a).mpr ha])
  simp only [Nat.add_zero, Nat.mod_eq_of_lt (phase_lt f a), Function.iterate_zero, id_eq] at hs
  rw [hc] at hs
  calc f^[p - phase f a] a = f^[p - phase f a] (f^[phase f a] c) := congrArg _ hs
    _ = f^[p] c := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hp]

/-- On a long cycle, some checkpoint lies within `2 * L` steps before each phase. -/
theorem exists_cycle_checkpoint
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    (x : α) {p : ℕ} (hK : 2 * L < p) (hp : p < cycleLength f x) :
    ∃ a ∈ H, a ∈ Function.periodicPts f ∧ canonicalCycle f a = canonicalCycle f x ∧
      phase f a ≤ p ∧ p - phase f a ≤ 2 * L := by
  let c := canonicalCycle f x
  have hzero : phase f c = 0 := by
    have hs := phase_shift f x (canonicalTime f x)
    rw [canonicalTime_spec] at hs
    have hm := phase_cancel f x
    rw [hs]
    exact hm
  have hlen : cycleLength f c = cycleLength f x := by
    have h := cycleLength_iterate f x (canonicalTime f x)
    rwa [canonicalTime_spec] at h
  let z := f^[p - (2 * L - 1)] c
  have hzlen : cycleLength f z = cycleLength f x := by
    rw [cycleLength_iterate, hlen]
  have hcover' : ∃ d < 2 * L, f^[d] z ∈ H := by
    rcases hcover z with ⟨i, j, hij, hj, he⟩ | h
    · have hr := depth_add_cycleLength_le_repeat f z hij he
      lia
    · exact h
  obtain ⟨d, hd, hmem⟩ := hcover'
  have ha : f^[d] z = f^[p - (2 * L - 1) + d] c := by
    rw [Nat.add_comm (p - (2 * L - 1)) d, Function.iterate_add_apply]
  refine ⟨_, hmem, ?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact (periodic_iterate_iff f c _).mpr
      (by simp [(transientDepth_eq_zero_iff f c).mpr (canonicalCycle_periodic f x)])
  · rw [ha, canonicalCycle_iterate]
    have h := canonicalCycle_iterate f x (canonicalTime f x)
    rw [canonicalTime_spec] at h
    exact h
  · rw [ha, phase_shift, hzero, hlen, Nat.zero_add, Nat.mod_eq_of_lt (by lia)]
    lia
  · rw [ha, phase_shift, hzero, hlen, Nat.zero_add, Nat.mod_eq_of_lt (by lia)]
    lia

end IteratedFunctions
