/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CheckpointForest

/-! # Short, nonmerging segments between refined checkpoints -/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Finite α] (f : α → α) (H : Finset α)

theorem forest_cycle_entry_mem {x : α} (hx : x ∈ checkpointHull f H) :
    f^[transientDepth f x] x ∈ forestMarks f H := by
  apply forestRoot_mem_marks f H (checkpointHull_iterate f H hx le_rfl)
  rw [transientDepth_iterate, Nat.sub_self]

theorem forest_iterate_mem_sources {x : α} (hx : x ∈ checkpointHull f H)
    {i : ℕ} (hi : i < transientDepth f x) : f^[i] x ∈ forestSources f H := by
  apply (mem_forestSources f H _).mpr
  refine ⟨checkpointHull_iterate f H hx hi.le, ?_⟩
  rw [transientDepth_iterate]
  lia

/-- A compressed edge ends at the next mark, no later than cycle entry. -/
structure IsForestEdge (x : α) (d : ℕ) : Prop where
  start_mem : x ∈ forestMarks f H
  pos : 0 < d
  le_depth : d ≤ transientDepth f x
  end_mem : f^[d] x ∈ forestMarks f H
  interior : ∀ i, 0 < i → i < d → f^[i] x ∉ forestMarks f H

theorem IsForestEdge.source {x : α} {d : ℕ} (h : IsForestEdge f H x d)
    {i : ℕ} (hi : i < d) : f^[i] x ∈ forestSources f H :=
  forest_iterate_mem_sources f H (forestMarks_subset_hull f H h.start_mem) (hi.trans_le h.le_depth)

/-- Applying checkpoint coverage after one step bounds each compressed edge by `2L`. -/
theorem exists_short_forest_edge {L : ℕ} (_hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {x : α} (hx : x ∈ forestMarks f H) (hd : 0 < transientDepth f x) :
    ∃ d ≤ 2 * L, IsForestEdge f H x d := by
  classical
  have hxS := forestMarks_subset_hull f H hx
  have hroot := forest_cycle_entry_mem f H hxS
  have hex : ∃ d, 0 < d ∧ f^[d] x ∈ forestMarks f H := ⟨_, hd, hroot⟩
  have hshort : ∃ t, 0 < t ∧ t ≤ 2 * L ∧ f^[t] x ∈ forestMarks f H := by
    rcases hcover (f x) with ⟨i, j, hij, hj, he⟩ | ⟨t, ht, hmem⟩
    · have hperiod := depth_add_cycleLength_le_repeat f (f x) hij he
      have hdepth : transientDepth f (f x) = transientDepth f x - 1 := by
        simpa only [Function.iterate_one] using transientDepth_iterate f x 1
      exact ⟨_, hd, by lia, hroot⟩
    · refine ⟨t + 1, by lia, by lia, ?_⟩
      rw [Function.iterate_succ_apply]
      exact subset_forestMarks f H hmem
  let d := Nat.find hex
  have hspec := Nat.find_spec hex
  have hdepth : d ≤ transientDepth f x := Nat.find_min' hex ⟨hd, hroot⟩
  obtain ⟨t, ht, htL, htm⟩ := hshort
  have hdt : d ≤ t := Nat.find_min' hex ⟨ht, htm⟩
  refine ⟨d, hdt.trans htL, hx, hspec.1, hdepth, hspec.2, ?_⟩
  intro i hi hid him
  exact Nat.find_min hex hid ⟨hi, him⟩

/-- Interiors of compressed edges are disjoint, including their starting marks. -/
theorem forest_edges_merge {x y : α} {d e : ℕ}
    (hx : IsForestEdge f H x d) (hy : IsForestEdge f H y e)
    {i j : ℕ} (hi : i < d) (hj : j < e) (he : f^[i] x = f^[j] y) :
    x = y ∧ i = j := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact ⟨he, rfl⟩
    | succ j =>
      have hnot := hy.interior (j + 1) (by lia) hj
      exact (hnot (he ▸ hx.start_mem)).elim
  | succ i ih =>
    cases j with
    | zero =>
      have hnot := hx.interior (i + 1) (by lia) hi
      exact (hnot (he.symm ▸ hy.start_mem)).elim
    | succ j =>
      have hpred : f^[i] x = f^[j] y := by
        apply forestPredecessor_unique f H (hx.source f H (by lia)) (hy.source f H (by lia))
          (z := f^[i + 1] x)
        · exact (Function.iterate_succ_apply' f i x).symm
        · exact (Function.iterate_succ_apply' f j y).symm.trans he.symm
        · exact hx.interior (i + 1) (by lia) hi
      obtain ⟨hxy, hij⟩ := ih (by lia) (by lia) hpred
      exact ⟨hxy, by lia⟩

/-- Last-predecessor keys identify compressed edges uniquely. -/
theorem forest_edge_last_injective {x y : α} {d e : ℕ}
    (hx : IsForestEdge f H x d) (hy : IsForestEdge f H y e)
    (he : f^[d - 1] x = f^[e - 1] y) : x = y ∧ d = e := by
  have h := forest_edges_merge f H hx hy (by have := hx.pos; lia) (by have := hy.pos; lia) he
  exact ⟨h.1, by have := hx.pos; have := hy.pos; lia⟩

/-- Every hull point is marked or belongs to a short compressed edge. -/
theorem forest_hull_partition {L : ℕ} (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {y : α} (hy : y ∈ checkpointHull f H) :
    y ∈ forestMarks f H ∨ ∃ a d i, IsForestEdge f H a d ∧
      d ≤ 2 * L ∧ i < d ∧ f^[i] a = y := by
  have visit (t : ℕ) : ∀ a ∈ forestMarks f H, t ≤ transientDepth f a →
      f^[t] a ∈ forestMarks f H ∨ ∃ b d i, IsForestEdge f H b d ∧
        d ≤ 2 * L ∧ i < d ∧ f^[i] b = f^[t] a := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro a ha ht
      by_cases hz : t = 0
      · subst t
        exact Or.inl ha
      obtain ⟨d, hd, hedge⟩ := exists_short_forest_edge f H hL hcover ha (by lia)
      by_cases htd : t < d
      · exact Or.inr ⟨a, d, t, hedge, hd, htd, rfl⟩
      have hdpos := hedge.pos
      have he : f^[t - d] (f^[d] a) = f^[t] a := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia : d ≤ t)]
      have hh := ih (t - d) (by lia) (f^[d] a) hedge.end_mem (by
        rw [transientDepth_iterate]
        lia)
      simpa only [he] using hh
  obtain ⟨a, ha, t, ht, rfl⟩ := (mem_checkpointHull f H y).mp hy
  exact visit t a (subset_forestMarks f H ha) ht

/-- A matched interior can be traced backwards as far as its lower endpoint. -/
theorem forest_backtrack_interior {a y : α} {d i j : ℕ}
    (ha : IsForestEdge f H a d) (hy : y ∈ checkpointHull f H)
    (hi : i < d) (hji : j ≤ i) (hj : j < transientDepth f y)
    (he : f^[i] a = f^[j] y) : f^[i - j] a = y := by
  induction j generalizing i with
  | zero => simpa only [Nat.sub_zero, Function.iterate_zero_apply] using he
  | succ j ih =>
    cases i with
    | zero => lia
    | succ i =>
      have hpred : f^[i] a = f^[j] y := by
        apply forestPredecessor_unique f H (ha.source f H (by lia))
          (forest_iterate_mem_sources f H hy (by lia)) (z := f^[i + 1] a)
        · exact (Function.iterate_succ_apply' f i a).symm
        · exact (Function.iterate_succ_apply' f j y).symm.trans he.symm
        · exact ha.interior (i + 1) (by lia) hi
      simpa only [Nat.succ_sub_succ_eq_sub] using ih (by lia) (by lia) (by lia) hpred

/-- Depth filtering makes any eligible last-predecessor match identify the containing edge. -/
theorem forest_segment_contains_of_depth {a y : α} {d k : ℕ}
    (ha : IsForestEdge f H a d) (hy : y ∈ checkpointHull f H)
    (hdepth : transientDepth f y ≤ transientDepth f a)
    (he : f^[k] y = f^[d - 1] a) : ∃ i < d, f^[i] a = y := by
  have hd : d - 1 < d := by have := ha.pos; lia
  have hlast := (mem_forestSources f H _).mp (ha.source f H hd)
  have hdy := transientDepth_iterate f y k
  have hda := transientDepth_iterate f a (d - 1)
  rw [he] at hdy
  have hbound := ha.le_depth
  have hk : k < transientDepth f y := by lia
  have hkd : k ≤ d - 1 := by lia
  exact ⟨d - 1 - k, by lia,
    forest_backtrack_interior f H ha hy hd hkd hk he.symm⟩

/-- A marked vertex reaches an edge interior only by passing its lower marked endpoint. -/
theorem forest_reaches_through_edge {a h : α} {d i t : ℕ}
    (ha : IsForestEdge f H a d) (hh : h ∈ forestMarks f H)
    (hi : i < d) (he : f^[t] h = f^[i] a) : ∃ u, f^[u] h = a := by
  induction i generalizing t with
  | zero => exact ⟨t, he⟩
  | succ i ih =>
    cases t with
    | zero => exact (ha.interior (i + 1) (by lia) hi (he ▸ hh)).elim
    | succ t =>
      have htarget := (mem_forestSources f H _).mp (ha.source f H hi)
      have hdepth := transientDepth_iterate f h (t + 1)
      rw [he] at hdepth
      have ht : t < transientDepth f h := by lia
      have hpred : f^[t] h = f^[i] a := by
        apply forestPredecessor_unique f H
          (forest_iterate_mem_sources f H (forestMarks_subset_hull f H hh) ht)
          (ha.source f H (by lia)) (z := f^[i + 1] a)
        · exact (Function.iterate_succ_apply' f t h).symm.trans he
        · exact (Function.iterate_succ_apply' f i a).symm
        · exact ha.interior (i + 1) (by lia) hi
      exact ih (by lia) hpred

theorem forest_transient_reachable_mem {x y : α} (hx : x ∈ checkpointHull f H)
    (hy : 0 < transientDepth f y) (hr : ∃ t, f^[t] x = y) : y ∈ checkpointHull f H := by
  obtain ⟨t, ht⟩ := hr
  have hd := transientDepth_iterate f x t
  rw [ht] at hd
  have hmem := checkpointHull_iterate f H hx (t := t) (by lia)
  exact ht ▸ hmem

/-- A transient target beyond the inspected prefix lies above a prefix checkpoint. -/
theorem checkpoint_before_distant_target {L : ℕ}
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {x y : α} (hy : 0 < transientDepth f y) (hr : ∃ t, f^[t] x = y)
    (hfar : ∀ i ≤ 2 * L, f^[i] x ≠ y) :
    ∃ d < 2 * L, f^[d] x ∈ H ∧ ∃ u, f^[u] (f^[d] x) = y := by
  obtain ⟨t, ht⟩ := hr
  have hgt : 2 * L < t := by by_contra h; exact hfar t (by lia) ht
  have hdepth := transientDepth_iterate f x t
  rw [ht] at hdepth
  rcases hcover x with ⟨i, j, hij, hj, he⟩ | ⟨d, hd, hmem⟩
  · have hrepeat := depth_add_cycleLength_le_repeat f x hij he
    lia
  · refine ⟨d, hd, hmem, t - d, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia : d ≤ t)]
    exact ht

end IteratedFunctions
