/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ScanSelection
public import Proofs.HittingTimes
import Mathlib.Tactic.Linarith

/-! # Canonical labels from one complete traversal of a short cycle -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

variable {n a w : ℕ}
noncomputable local instance shortCycleStateOrder : LinearOrder (State n) := stateOrder n

noncomputable def shortRepresentative (f : State n → State n) (K : ℕ) (x : State n) : State n :=
  scanMin (fun j : Fin (K + 1) => f^[j.val] x) x (K + 1)

def firstIndex {R : ℕ} (flags : Fin R → Bool) : BitVec w :=
  word (chooseFirst flags (fun j bit => (BitVec.ofNat w j.val).getLsbD bit.val) (fun _ => false))

theorem firstIndex_spec {R : ℕ} (flags : Fin R → Bool) (j : Fin R) (hj : flags j = true)
    (hfirst : ∀ i : Fin R, i.val < j.val → flags i = false) :
    firstIndex (w := w) flags = BitVec.ofNat w j.val := by
  rw [firstIndex, chooseFirst_spec flags _ _ j hj hfirst, word_bits]

noncomputable def shortLength (f : State n → State n) (K : ℕ) (x : State n) : BitVec w :=
  firstIndex fun j : Fin (K + 1) => decide (0 < j.val ∧ f^[j.val] x = x)

noncomputable def shortTime (f : State n → State n) (K : ℕ) (x : State n) : BitVec w :=
  firstIndex fun j : Fin (K + 1) => decide (f^[j.val] x = shortRepresentative f K x)

theorem shortRepresentative_spec (f : State n → State n) (K : ℕ) (x : State n)
    (hx : x ∈ Function.periodicPts f) (hK : cycleLength f x ≤ K) :
    shortRepresentative f K x = canonicalCycle f x := by
  classical
  have hμ := (transientDepth_eq_zero_iff f x).mpr hx
  have hmem (j : ℕ) : f^[j] x ∈ cycleSet f x := by
    rw [mem_cycleSet_iff, hμ, Function.iterate_zero_apply]
    exact Function.iterate_mem_periodicOrbit hx j
  have hs := @scanMin_spec (State n) (stateOrder n) (K + 1)
    (fun j : Fin (K + 1) => f^[j.val] x) x (K + 1)
  apply @le_antisymm (State n) (stateOrder n).toPartialOrder
  · have ht := canonicalTime_lt_cycleLength f x hx
    have h := hs.2.2 ⟨canonicalTime f x, by lia⟩ (by simp; lia)
    change toLex (shortRepresentative f K x) ≤ toLex (f^[canonicalTime f x] x) at h
    rw [canonicalTime_spec] at h
    exact h
  · apply canonicalCycle_le f x
    rcases hs.1 with hh | ⟨j, _, hh⟩
    · rw [show shortRepresentative f K x = x from hh]
      simpa using hmem 0
    · rw [show shortRepresentative f K x = _ from hh]
      exact hmem j.val

theorem shortLength_spec (f : State n → State n) (K : ℕ) (x : State n)
    (hx : x ∈ Function.periodicPts f) (hK : cycleLength f x ≤ K) :
    shortLength (w := w) f K x = BitVec.ofNat w (cycleLength f x) := by
  let j : Fin (K + 1) := ⟨cycleLength f x, by lia⟩
  apply firstIndex_spec _ j
  · apply decide_eq_true
    refine ⟨cycleLength_pos f x, ?_⟩
    have h : f^[cycleLength f x] (f^[transientDepth f x] x) = f^[transientDepth f x] x :=
      cycleLength_periodic f x
    change f^[cycleLength f x] x = x
    simpa only [(transientDepth_eq_zero_iff f x).mpr hx, Function.iterate_zero_apply] using h
  · intro i hi
    apply decide_eq_false
    rintro ⟨hip, he⟩
    have hm := Function.IsPeriodicPt.minimalPeriod_le hip he
    have hell : Function.minimalPeriod f x = cycleLength f x := by
      simp only [cycleLength, (transientDepth_eq_zero_iff f x).mpr hx,
        Function.iterate_zero_apply]
    rw [hell] at hm
    have : i.val < cycleLength f x := hi
    lia

theorem shortTime_spec (f : State n → State n) (K : ℕ) (x : State n)
    (hx : x ∈ Function.periodicPts f) (hK : cycleLength f x ≤ K) :
    shortTime (w := w) f K x = BitVec.ofNat w (canonicalTime f x) := by
  unfold shortTime
  rw [shortRepresentative_spec f K x hx hK]
  let j : Fin (K + 1) := ⟨canonicalTime f x,
    (canonicalTime_lt_cycleLength f x hx).trans_le (by lia)⟩
  exact firstIndex_spec _ j (by simp [j, canonicalTime_spec])
    (fun i hi => decide_eq_false (canonicalTime_min f x hi))

theorem synthesis_firstIndex {R : ℕ} (s : Set (State a → Bool))
    (flags : State a → Fin R → Bool) (hf : ∀ j, (fun x => flags x j) ∈ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) :
    Synthesis Boolean.interpretation s (wordWires fun x => firstIndex (w := w) (flags x))
      (R * (4 * w)) := by
  have h := synthesis_chooseRecord (w := w) s (fun x j => flags x j.rev)
    (fun _ j bit => (BitVec.ofNat w j.rev.val).getLsbD bit.val) (fun _ _ => false)
    (fun j => hf j.rev) (fun _ _ => hc _) (fun _ => hc false)
  simpa only [wordWires, firstIndex, chooseFirst, word_bit] using h

/-- Short-cycle work, assuming the orbit prefix is already available. -/
theorem synthesis_short_labels (s : Set (State a → Bool)) (f : State n → State n)
    (init : State a → State n) (K : ℕ)
    (hp : ∀ j : Fin (K + 1), ∀ bit, (fun x => f^[j.val] (init x) bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) :
    Synthesis Boolean.interpretation s
      (wires (fun x => shortRepresentative f K (init x)) ∪
        wordWires (fun x => shortLength (w := w) f K (init x)) ∪
        wordWires (fun x => shortTime (w := w) f K (init x)))
      ((K + 1) * (30 * (n + w + 1))) := by
  let rep := fun x => shortRepresentative f K (init x)
  have hm := synthesis_scanMin s (fun x j => f^[j.val] (init x)) init hp (hp 0)
  let src := s ∪ wires rep
  let flags := fun x (j : Fin (K + 1)) => decide (0 < j.val ∧ f^[j.val] (init x) = init x)
  have hflags : Synthesis Boolean.interpretation src (Set.range fun j x => flags x j)
      ((K + 1) * (6 * n + 1)) := by
    have h := Synthesis.family (I := Boolean.interpretation) (s := src)
      (fun j x => flags x j) (fun _ => 6 * n + 1) (fun j => ?_)
    · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul] using h
    · by_cases hj : 0 < j.val
      · simpa only [flags, hj, true_and] using
          synthesis_bits_eq src (fun x => f^[j.val] (init x)) init
            (by rintro _ ⟨bit, rfl⟩; exact Or.inl (hp j bit))
            (by rintro _ ⟨bit, rfl⟩; exact Or.inl (hp 0 bit))
      · have h := Synthesis.const (s := src) false
        simp only [flags, hj, false_and, decide_false]
        exact h.mono Set.Subset.rfl Set.Subset.rfl (by lia)
  have hl := synthesis_firstIndex (w := w) (src ∪ Set.range (fun j x => flags x j)) flags
    (fun j => Or.inr ⟨j, rfl⟩) (fun b => Or.inl (Or.inl (hc b)))
  let flags' := fun x (j : Fin (K + 1)) => decide (f^[j.val] (init x) = rep x)
  have hflags' := Synthesis.family (I := Boolean.interpretation) (s := src)
    (fun j x => flags' x j) (fun _ => 6 * n + 1) (fun j =>
      synthesis_bits_eq src (fun x => f^[j.val] (init x)) rep
        (by rintro _ ⟨bit, rfl⟩; exact Or.inl (hp j bit)) (fun _ h => Or.inr h))
  have ht := synthesis_firstIndex (w := w) (src ∪ Set.range (fun j x => flags' x j)) flags'
    (fun j => Or.inr ⟨j, rfl⟩) (fun b => Or.inl (Or.inl (hc b)))
  have hall := hm.comp ((hflags.trans hl).union (hflags'.trans ht))
  apply hall.mono Set.Subset.rfl ?_ ?_
  · intro g hg
    rcases hg with (hg | hg) | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)
    · exact Or.inr (Or.inr hg)
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    nlinarith

end IteratedFunctions
