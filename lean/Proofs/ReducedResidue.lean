/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.PhaseArithmetic
public import Proofs.LinearArithmetic

/-! # Linear-size modular subtraction of reduced residues -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n w : ℕ}

/-- No general division is needed when both operands are already reduced. -/
def subtractResidues (a b d : BitVec w) : BitVec w :=
  if a.ult b then d - (b - a) else a - b

theorem subtractResidues_toNat (a b d : BitVec w)
    (ha : a.toNat < d.toNat) (hb : b.toNat < d.toNat) :
    (subtractResidues a b d).toNat = subtractModNat a.toNat b.toNat d.toNat := by
  unfold subtractResidues subtractModNat
  rw [Nat.mod_eq_of_lt hb]
  by_cases h : a.toNat < b.toNat
  · have hba : a ≤ b := by change a.toNat ≤ b.toNat; lia
    have hsub : (b - a).toNat = b.toNat - a.toNat := BitVec.toNat_sub_of_le hba
    have hle : b - a ≤ d := by change (b - a).toNat ≤ d.toNat; rw [hsub]; lia
    simp only [BitVec.ult, h, decide_true, ite_true, BitVec.toNat_sub_of_le hle, hsub]
    rw [Nat.mod_eq_of_lt (by lia : a.toNat + d.toNat - b.toNat < d.toNat)]
    lia
  · have hle : b ≤ a := by change b.toNat ≤ a.toNat; lia
    simp only [BitVec.ult, h, decide_false, Bool.false_eq_true, ite_false,
      BitVec.toNat_sub_of_le hle]
    rw [show a.toNat + d.toNat - b.toNat = a.toNat - b.toNat + d.toNat by lia,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by lia : a.toNat - b.toNat < d.toNat)]

/-- Three shared-carry subtractions, a comparison, and one word selection. -/
theorem synthesis_subtractResidues (s : Set (State n → Bool))
    (a b d : State n → BitVec w)
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) (hd : wordWires d ⊆ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => subtractResidues (a x) (b x) (d x)) (140 * (w + 1)) := by
  have hba := synthesis_sub_linear s b a (fun i => hb ⟨i, rfl⟩) (fun i => ha ⟨i, rfl⟩)
  let s1 := s ∪ wordWires (fun x => b x - a x)
  have hwrap := synthesis_sub_linear s1 d (fun x => b x - a x)
    (fun i => Or.inl (hd ⟨i, rfl⟩)) (fun i => Or.inr ⟨i, rfl⟩)
  have hab := synthesis_sub_linear s a b (fun i => ha ⟨i, rfl⟩) (fun i => hb ⟨i, rfl⟩)
  have hlt := synthesis_ult s a b (fun i => ha ⟨i, rfl⟩) (fun i => hb ⟨i, rfl⟩)
  let src := s ∪ ((wordWires (fun x => d x - (b x - a x)) ∪
    wordWires (fun x => a x - b x)) ∪ {fun x => (a x).ult (b x)})
  have hout := synthesis_word_mux src (fun x => d x - (b x - a x))
    (fun x => a x - b x) (fun x => (a x).ult (b x)) (Or.inr (Or.inr rfl))
    (fun i => Or.inr (Or.inl (Or.inl ⟨i, rfl⟩)))
    (fun i => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩)))
  exact ((((hba.trans hwrap).union hab).union hlt).trans hout).mono
    Set.Subset.rfl Set.Subset.rfl (by lia)

end IteratedFunctions
