/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.RecordCircuits
public import Proofs.BatchFinish
public import Proofs.CycleLabels

/-! # Linear scans for a minimum state and the first marked position -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

/-- Lexicographic state order, with coordinate zero compared first. -/
noncomputable abbrev stateOrder (n : ℕ) : LinearOrder (State n) :=
  LinearOrder.lift' toLex (fun _ _ h => h)

section MinScan
variable {α : Type*} [LinearOrder α] {R : ℕ}

def scanMin (records : Fin R → α) (fallback : α) : ℕ → α
  | 0 => fallback
  | t + 1 => if h : t < R then min (records ⟨t, h⟩) (scanMin records fallback t)
    else scanMin records fallback t

theorem scanMin_spec (records : Fin R → α) (fallback : α) (t : ℕ) :
    (scanMin records fallback t = fallback ∨
      ∃ j : Fin R, j.val < t ∧ scanMin records fallback t = records j) ∧
    scanMin records fallback t ≤ fallback ∧
      ∀ j : Fin R, j.val < t → scanMin records fallback t ≤ records j := by
  induction t with
  | zero => exact ⟨Or.inl rfl, le_rfl, fun j hj => by lia⟩
  | succ t ih =>
    by_cases ht : t < R
    · rw [scanMin, dite_eq_left ht]
      constructor
      · rcases min_cases (records ⟨t, ht⟩) (scanMin records fallback t) with h | h
        · exact Or.inr ⟨⟨t, ht⟩, by simp, h.1⟩
        · rcases ih.1 with hh | ⟨j, hj, he⟩
          · exact Or.inl (h.1.trans hh)
          · exact Or.inr ⟨j, by lia, h.1.trans he⟩
      · refine ⟨(min_le_right _ _).trans ih.2.1, ?_⟩
        intro j hj
        by_cases he : j.val = t
        · have : j = ⟨t, ht⟩ := Fin.ext he
          subst j
          exact min_le_left _ _
        · exact (min_le_right _ _).trans (ih.2.2 j (by lia))
    · rw [scanMin, dite_eq_right ht]
      refine ⟨?_, ih.2.1, fun j _ => ih.2.2 j (by have := j.isLt; lia)⟩
      rcases ih.1 with h | ⟨j, hj, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by lia, he⟩

end MinScan

variable {n a R w : ℕ}

/-- A minimum scan shares each comparison across all output bits. -/
theorem synthesis_scanMin (s : Set (State a → Bool))
    (records : State a → Fin R → State n) (fallback : State a → State n)
    (hr : ∀ j bit, (fun x => records x j bit) ∈ s)
    (hf : ∀ bit, (fun x => fallback x bit) ∈ s) :
    letI := stateOrder n
    Synthesis Boolean.interpretation s
      (wires fun x => scanMin (records x) (fallback x) R) (R * (13 * n + 1)) := by
  let := stateOrder n
  let values := fun t x => scanMin (records x) (fallback x) t
  let q := fun t => wires (values t)
  have hz : q 0 ⊆ s := by rintro _ ⟨bit, rfl⟩; exact hf bit
  have hs := Synthesis.steps (I := Boolean.interpretation) q (13 * n + 1) R hz (fun t ht => ?_)
  · exact hs.mono Set.Subset.rfl (Synthesis.mem_stages q R) le_rfl
  · let src := s ∪ Synthesis.stages q t
    have hav (i : Fin n) : (fun x => values t x i) ∈ src :=
      Or.inr (Synthesis.mem_stages q t ⟨i, rfl⟩)
    have hl := synthesis_lexLess src (fun x => records x ⟨t, ht⟩) (values t)
      (fun i => Or.inl (hr _ i)) hav
    have hm := synthesis_bits_mux (src ∪ {fun x => lexLess (records x ⟨t, ht⟩) (values t x)})
      (fun x => records x ⟨t, ht⟩) (values t)
      (fun x => lexLess (records x ⟨t, ht⟩) (values t x))
      (by rintro _ ⟨bit, rfl⟩; exact Or.inl (Or.inl (hr _ bit)))
      (by rintro _ ⟨bit, rfl⟩; exact Or.inl (hav bit)) (Or.inr rfl)
    have he (x : State a) :
        (if lexLess (records x ⟨t, ht⟩) (values t x) then records x ⟨t, ht⟩ else values t x) =
          values (t + 1) x := by
      change _ = scanMin (records x) (fallback x) (t + 1)
      rw [scanMin, dite_eq_left ht]
      by_cases hh : lexLess (records x ⟨t, ht⟩) (values t x) = true
      · rw [ite_eq_left hh]
        refine (min_eq_left ?_).symm
        change toLex (records x ⟨t, ht⟩) ≤ toLex (values t x)
        exact ((lexLess_eq_true_iff _ _).mp hh).le
      · rw [ite_eq_right hh]
        refine (min_eq_right ?_).symm
        change toLex (values t x) ≤ toLex (records x ⟨t, ht⟩)
        exact le_of_not_gt (fun h => hh ((lexLess_eq_true_iff _ _).mpr h))
    have h := hl.trans hm
    simp only [he] at h
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by lia)

theorem chooseRecord_eq_of_last {α : Type*} (flags : Fin R → Bool) (records : Fin R → α)
    (fallback : α) (j : Fin R) (hj : flags j = true) (t : ℕ) (hjt : j.val < t)
    (hlast : ∀ i : Fin R, j.val < i.val → i.val < t → flags i = false) :
    chooseRecord flags records fallback t = records j := by
  induction t with
  | zero => lia
  | succ t ih =>
    by_cases ht : t < R
    · rw [chooseRecord, dite_eq_left ht]
      by_cases he : j.val = t
      · have he' : (⟨t, ht⟩ : Fin R) = j := Fin.ext he.symm
        simp only [he', hj, ite_true]
      · simp only [hlast ⟨t, ht⟩ (by simp; lia) (by simp), Bool.false_eq_true, ite_false]
        exact ih (by lia) (fun i hi hit => hlast i hi (by lia))
    · rw [chooseRecord, dite_eq_right ht]
      exact ih (by have := j.isLt; lia) (fun i hi hit => hlast i hi (by lia))

def chooseFirst {α : Type*} (flags : Fin R → Bool) (records : Fin R → α) (fallback : α) : α :=
  chooseRecord (fun j => flags j.rev) (fun j => records j.rev) fallback R

theorem chooseFirst_spec {α : Type*} (flags : Fin R → Bool) (records : Fin R → α)
    (fallback : α) (j : Fin R) (hj : flags j = true)
    (hfirst : ∀ i : Fin R, i.val < j.val → flags i = false) :
    chooseFirst flags records fallback = records j := by
  have h := chooseRecord_eq_of_last (fun i => flags i.rev) (fun i => records i.rev)
    fallback j.rev (by simpa using hj) R j.rev.isLt (fun i hi _ => ?_)
  · simpa only [chooseFirst, Fin.rev_rev] using h
  · apply hfirst
    simp only [Fin.val_rev] at hi ⊢
    have := i.isLt
    have := j.isLt
    lia

end IteratedFunctions
