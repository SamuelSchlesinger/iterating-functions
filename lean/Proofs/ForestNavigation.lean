/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ForestSegments
public import Proofs.ForestIntervals

/-!
# Navigation through a compressed checkpoint forest

A target anchor is either the target itself, when marked, or the lower
endpoint of an edge whose last-predecessor key appears in the target's
short prefix. Filtering the latter matches by depth permits arbitrary
record selection. A final short-prefix check excludes side branches
outside the checkpoint hull.

The query theorem is semantic. The Boolean implementation must still
charge dictionary lookup, record selection, and all three short prefixes.
-/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Finite α] (f : α → α) (H : Finset α) (L : ℕ)

/-- A candidate lower endpoint obtained from a marked target or a depth-filtered edge key. -/
def ForestAnchor (y a : α) : Prop :=
  (y ∈ forestMarks f H ∧ a = y) ∨
    ∃ d k, IsForestEdge f H a d ∧ d ≤ 2 * L ∧ k ≤ 2 * L ∧
      transientDepth f y ≤ transientDepth f a ∧ f^[k] y = f^[d - 1] a

theorem exists_forest_anchor (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    {y : α} (hy : y ∈ checkpointHull f H) : ∃ a, ForestAnchor f H L y a := by
  rcases forest_hull_partition f H hL hcover hy with hm | ⟨a, d, i, he, hd, hi, hiy⟩
  · exact ⟨y, Or.inl ⟨hm, rfl⟩⟩
  · refine ⟨a, Or.inr ⟨d, d - 1 - i, he, hd, by lia, ?_, ?_⟩⟩
    · rw [← hiy, transientDepth_iterate]
      exact Nat.sub_le _ _
    · rw [← hiy, ← Function.iterate_add_apply]
      congr 1
      lia

/-- All eligible keys are safe on hull points; selection need not choose the first key. -/
theorem forest_anchor_contains {y a : α} (hy : y ∈ checkpointHull f H)
    (ha : ForestAnchor f H L y a) :
    a ∈ forestMarks f H ∧ (∃ i ≤ 2 * L, f^[i] a = y) ∧
      ∀ h ∈ forestMarks f H, (∃ t, f^[t] h = y) → ∃ t, f^[t] h = a := by
  rcases ha with ⟨hm, rfl⟩ | ⟨d, k, hedge, hd, _, hdepth, he⟩
  · exact ⟨hm, ⟨0, Nat.zero_le _, rfl⟩, fun _ _ hr => hr⟩
  · obtain ⟨i, hi, hiy⟩ := forest_segment_contains_of_depth f H hedge hy hdepth he
    refine ⟨hedge.start_mem, ⟨i, hi.le.trans hd, hiy⟩, ?_⟩
    intro h hh hr
    obtain ⟨t, ht⟩ := hr
    exact forest_reaches_through_edge f H hedge hh hi (ht.trans hiy.symm)

omit [Finite α] in
/-- A target beyond a prefix remains reachable from every state in that prefix. -/
theorem reaches_from_prefix {x y h : α} (hr : ∃ t, f^[t] x = y)
    (hfar : ∀ i ≤ 2 * L, f^[i] x ≠ y) (hp : ∃ d ≤ 2 * L, f^[d] x = h) :
    ∃ t, f^[t] h = y := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨d, hd, rfl⟩ := hp
  have hgt : 2 * L < t := by by_contra h; exact hfar t (by lia) ht
  refine ⟨t - d, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by lia : d ≤ t)]
  exact ht

/-- Exact transient reachability using two selected records and one verification prefix. -/
theorem forest_navigation_spec (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H)
    (low high : α → Fin (Nat.card α))
    (hinterval : ∀ x y, (low y ≤ low x ∧ low x ≤ high y) ↔
      ∃ t ≤ transientDepth f x, f^[t] x = y)
    (x y h a : α) (hy : 0 < transientDepth f y)
    (foundH foundA : Bool)
    (hHsound : foundH = true → h ∈ forestMarks f H ∧ ∃ d ≤ 2 * L, f^[d] x = h)
    (hHcomplete : (∃ d ≤ 2 * L, f^[d] x ∈ forestMarks f H) → foundH = true)
    (hAsound : foundA = true → ForestAnchor f H L y a)
    (hAcomplete : (∃ b, ForestAnchor f H L y b) → foundA = true) :
    (∃ t, f^[t] x = y) ↔ (∃ i ≤ 2 * L, f^[i] x = y) ∨
      (foundH = true ∧ foundA = true ∧ (∃ i ≤ 2 * L, f^[i] a = y) ∧
        low a ≤ low h ∧ low h ≤ high a) := by
  constructor
  · intro hr
    by_cases hshort : ∃ i ≤ 2 * L, f^[i] x = y
    · exact Or.inl hshort
    have hfar : ∀ i ≤ 2 * L, f^[i] x ≠ y := by
      intro i hi he
      exact hshort ⟨i, hi, he⟩
    obtain ⟨d, hd, hmem, _⟩ := checkpoint_before_distant_target f H hcover hy hr hfar
    have hfound : foundH = true :=
      hHcomplete ⟨d, hd.le, subset_forestMarks f H hmem⟩
    obtain ⟨hh, hprefix⟩ := hHsound hfound
    have hreach := reaches_from_prefix f L hr hfar hprefix
    have hyS := forest_transient_reachable_mem f H (forestMarks_subset_hull f H hh) hy hreach
    have hafound := hAcomplete (exists_forest_anchor f H L hL hcover hyS)
    obtain ⟨_, hverify, hthrough⟩ := forest_anchor_contains f H L hyS (hAsound hafound)
    obtain ⟨t, ht⟩ := hthrough h hh hreach
    have haPos : 0 < transientDepth f a := by
      obtain ⟨i, _, hi⟩ := hverify
      have hh := transientDepth_iterate f a i
      rw [hi] at hh
      lia
    have hdepth := transientDepth_iterate f h t
    rw [ht] at hdepth
    exact Or.inr ⟨hfound, hafound, hverify, (hinterval h a).mpr ⟨t, by lia, ht⟩⟩
  · rintro (⟨i, _, hi⟩ | ⟨hfound, _, ⟨i, _, hi⟩, hlo, hhi⟩)
    · exact ⟨i, hi⟩
    · obtain ⟨_, d, _, hd⟩ := hHsound hfound
      obtain ⟨t, _, ht⟩ := (hinterval h a).mp ⟨hlo, hhi⟩
      refine ⟨i + t + d, ?_⟩
      rw [Function.iterate_add_apply, hd, Function.iterate_add_apply, ht, hi]

/-- The finite table stores one short edge for each nonroot marked vertex. -/
structure ForestEdgeTable where
  count : ℕ
  start : Fin count → α
  length : Fin count → ℕ
  edge : ∀ j, IsForestEdge f H (start j) (length j)
  short : ∀ j, length j ≤ 2 * L
  start_injective : Function.Injective start
  complete : ∀ a ∈ forestMarks f H, 0 < transientDepth f a → ∃ j, start j = a
  card_le : count ≤ (forestMarks f H).card

theorem exists_forest_edge_table (hL : 0 < L)
    (hcover : ∀ x, Repeats f x L ∨ ∃ t < 2 * L, f^[t] x ∈ H) :
    Nonempty (ForestEdgeTable f H L) := by
  classical
  let S := (forestMarks f H).filter fun a => 0 < transientDepth f a
  let start : Fin S.card → α := fun j => (S.equivFin.symm j).val
  have hstart (j : Fin S.card) : start j ∈ forestMarks f H ∧ 0 < transientDepth f (start j) :=
    Finset.mem_filter.mp (S.equivFin.symm j).property
  have hex (j : Fin S.card) : ∃ d ≤ 2 * L, IsForestEdge f H (start j) d :=
    exists_short_forest_edge f H hL hcover (hstart j).1 (hstart j).2
  choose length hs he using hex
  refine ⟨⟨S.card, start, length, he, hs, ?_, ?_, Finset.card_le_card (Finset.filter_subset _ _)⟩⟩
  · intro i j hij
    exact S.equivFin.symm.injective (Subtype.ext hij)
  · intro a ha hd
    exact ⟨S.equivFin ⟨a, Finset.mem_filter.mpr ⟨ha, hd⟩⟩, by simp [start]⟩

namespace ForestEdgeTable

variable {f H L} (table : ForestEdgeTable f H L)

def key (j : Fin table.count) : α := f^[table.length j - 1] (table.start j)

theorem key_injective : Function.Injective table.key := by
  intro i j he
  exact table.start_injective (forest_edge_last_injective f H (table.edge i) (table.edge j) he).1

/-- The edge dictionary and the depth filter characterize exactly the edge-anchor candidates. -/
theorem anchor_iff (y a : α) : ForestAnchor f H L y a ↔
    (y ∈ forestMarks f H ∧ a = y) ∨ ∃ j k, table.start j = a ∧ k ≤ 2 * L ∧
      transientDepth f y ≤ transientDepth f a ∧ f^[k] y = table.key j := by
  constructor
  · rintro (hm | ⟨d, k, hedge, hd, hk, hdepth, he⟩)
    · exact Or.inl hm
    · have haPos : 0 < transientDepth f a := lt_of_lt_of_le hedge.pos hedge.le_depth
      obtain ⟨j, hj⟩ := table.complete a hedge.start_mem haPos
      have hedge' : IsForestEdge f H a (table.length j) := hj ▸ table.edge j
      have hdEq : d = table.length j := by
        apply le_antisymm
        · by_contra h
          exact hedge.interior (table.length j) hedge'.pos (by lia) hedge'.end_mem
        · by_contra h
          exact hedge'.interior d hedge.pos (by lia) hedge.end_mem
      exact Or.inr ⟨j, k, hj, hk, hdepth, by simpa only [key, hj, hdEq] using he⟩
  · rintro (hm | ⟨j, k, rfl, hk, hdepth, he⟩)
    · exact Or.inl hm
    · exact Or.inr ⟨table.length j, k, table.edge j, table.short j, hk, hdepth, he⟩

end ForestEdgeTable

end IteratedFunctions
