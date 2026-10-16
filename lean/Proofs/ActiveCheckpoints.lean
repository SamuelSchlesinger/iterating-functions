/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Checkpoints
public import Proofs.CycleLabels

/-! # Charging checkpoints only to long transients and long cycles -/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Fintype α] (f : α → α)

/-- Deep transient states and the vertices of long cycles. -/
noncomputable def activeVertices (L : ℕ) : Finset α := by
  classical
  exact Finset.univ.filter fun x => L ≤ transientDepth f x ∨
    x ∈ Function.periodicPts f ∧ L ≤ cycleLength f x

theorem mem_activeVertices (L : ℕ) (x : α) :
    x ∈ activeVertices f L ↔ L ≤ transientDepth f x ∨
      x ∈ Function.periodicPts f ∧ L ≤ cycleLength f x := by
  classical
  simp only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Packing paths inside the active set costs at most `Q_L/L` checkpoints.
The set need not be forward invariant. A prefix of `4L` states compensates
for the shallow uncharged tail before reaching a cycle. -/
theorem exists_active_checkpoints (L : ℕ) (hL : 0 < L) :
    ∃ H : Finset α, H ⊆ activeVertices f L ∧ H.card * L ≤ (activeVertices f L).card ∧
      ∀ x, Repeats f x (4 * L) ∨ ∃ d < 4 * L, f^[d] x ∈ H := by
  obtain ⟨H, hH, hc, hcover⟩ := exists_checkpoints_on f (activeVertices f L) hL
  refine ⟨H, hH, hc, fun x => ?_⟩
  by_cases hd : 2 * L ≤ transientDepth f x
  · have hprefix (i : Fin L) : f^[i.val] x ∈ activeVertices f L := by
      apply (mem_activeVertices f L _).mpr
      left
      rw [transientDepth_iterate]
      have := i.isLt
      lia
    rcases hcover x hprefix with ⟨i, j, hij, hj, he⟩ | ⟨d, hd, hm⟩
    · exact Or.inl ⟨i, j, hij, by lia, he⟩
    · exact Or.inr ⟨d, by lia, hm⟩
  · by_cases hl : cycleLength f x < L
    · refine Or.inl ⟨transientDepth f x, transientDepth f x + cycleLength f x,
        by have := cycleLength_pos f x; lia, by lia, ?_⟩
      have hp := cycleLength_periodic f x
      change f^[cycleLength f x] (f^[transientDepth f x] x) = _ at hp
      simpa only [← Function.iterate_add_apply, Nat.add_comm] using hp.symm
    · let y := f^[transientDepth f x] x
      have hprefix (i : Fin L) : f^[i.val] y ∈ activeVertices f L := by
        apply (mem_activeVertices f L _).mpr
        right
        constructor
        · dsimp [y]
          rw [← Function.iterate_add_apply, periodic_iterate_iff]
          lia
        · rw [cycleLength_iterate]
          dsimp [y]
          rw [cycleLength_iterate]
          lia
      rcases hcover y hprefix with ⟨i, j, hij, hj, he⟩ | ⟨d, ht, hm⟩
      · refine Or.inl ⟨i + transientDepth f x, j + transientDepth f x,
          by lia, by lia, ?_⟩
        simpa only [Function.iterate_add_apply] using he
      · refine Or.inr ⟨d + transientDepth f x, by lia, ?_⟩
        simpa only [Function.iterate_add_apply] using hm

end IteratedFunctions
