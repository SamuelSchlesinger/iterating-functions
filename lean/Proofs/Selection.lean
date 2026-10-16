/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Synthesis

/-!
# Selecting one successful record

A linear scan retains the last flagged record. This avoids a quadratic
all-pairs priority test, and works with any number of flagged records.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

universe u
variable {α : Type u} {R w n : ℕ}

/-- Retain the last flagged record among the first `t` positions. -/
def chooseRecord (flags : Fin R → Bool) (records : Fin R → α) (fallback : α) : ℕ → α
  | 0 => fallback
  | t + 1 => if h : t < R then
      if flags ⟨t, h⟩ then records ⟨t, h⟩ else chooseRecord flags records fallback t
    else chooseRecord flags records fallback t

/-- Applying a fixed encoding commutes with record selection. -/
theorem chooseRecord_map {β : Type*} (g : α → β) (flags : Fin R → Bool)
    (records : Fin R → α) (fallback : α) (t : ℕ) :
    g (chooseRecord flags records fallback t) =
      chooseRecord flags (g ∘ records) (g fallback) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [chooseRecord]
    split_ifs <;> simp only [Function.comp_apply, ih]

/-- If a flag is present, the scan returns a record carrying a true flag. -/
theorem chooseRecord_spec (flags : Fin R → Bool) (records : Fin R → α) (fallback : α)
    (t : ℕ) (hex : ∃ j : Fin R, j.val < t ∧ flags j = true) :
    ∃ j : Fin R, j.val < t ∧ flags j = true ∧
      chooseRecord flags records fallback t = records j := by
  induction t with
  | zero => obtain ⟨j, hj, _⟩ := hex; lia
  | succ t ih =>
    by_cases ht : t < R
    · by_cases hf : flags ⟨t, ht⟩ = true
      · exact ⟨⟨t, ht⟩, by simp, hf, by simp [chooseRecord, ht, hf]⟩
      · have hex' : ∃ j : Fin R, j.val < t ∧ flags j = true := by
          obtain ⟨j, hj, hflag⟩ := hex
          refine ⟨j, ?_, hflag⟩
          have hne : j.val ≠ t := fun h => hf ((Fin.ext h : j = ⟨t, ht⟩) ▸ hflag)
          lia
        obtain ⟨j, hj, hflag, hout⟩ := ih hex'
        exact ⟨j, by lia, hflag, by simp [chooseRecord, ht, hf, hout]⟩
    · have hex' : ∃ j : Fin R, j.val < t ∧ flags j = true := by
        obtain ⟨j, _, hflag⟩ := hex
        exact ⟨j, by have := j.isLt; lia, hflag⟩
      obtain ⟨j, hj, hflag, hout⟩ := ih hex'
      exact ⟨j, by lia, hflag, by simp [chooseRecord, ht, hout]⟩

/-- Selecting an available record costs four gates per record bit. -/
theorem synthesis_chooseRecord (s : Set ((Fin n → Bool) → Bool))
    (flags : (Fin n → Bool) → Fin R → Bool)
    (records : (Fin n → Bool) → Fin R → Fin w → Bool)
    (fallback : (Fin n → Bool) → Fin w → Bool)
    (hf : ∀ j, (fun x => flags x j) ∈ s)
    (hr : ∀ j bit, (fun x => records x j bit) ∈ s)
    (hzero : ∀ bit, (fun x => fallback x bit) ∈ s) :
    Synthesis Boolean.interpretation s
      (Set.range fun bit x => chooseRecord (flags x) (records x) (fallback x) R bit)
      (R * (4 * w)) := by
  let q := fun t => Set.range fun bit x =>
    chooseRecord (flags x) (records x) (fallback x) t bit
  have h0 : q 0 ⊆ s := by rintro _ ⟨bit, rfl⟩; exact hzero bit
  have hs := Synthesis.steps (I := Boolean.interpretation) (s := s) q (4 * w) R h0
    (fun t ht => ?_)
  · exact hs.mono Set.Subset.rfl (Synthesis.mem_stages q R) le_rfl
  · have h := Synthesis.family (I := Boolean.interpretation) (s := s ∪ Synthesis.stages q t)
      (fun bit x => if flags x ⟨t, ht⟩ then records x ⟨t, ht⟩ bit
        else chooseRecord (flags x) (records x) (fallback x) t bit)
      (fun _ => 4) (fun bit => Synthesis.mux
        (Or.inl (hf ⟨t, ht⟩)) (Or.inl (hr ⟨t, ht⟩ bit))
        (Or.inr (Synthesis.mem_stages q t ⟨bit, rfl⟩)))
    simpa [q, chooseRecord, ht, ite_apply, Nat.mul_comm] using h

end IteratedFunctions
