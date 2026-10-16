/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Arithmetic
public import Mathlib.Data.List.OfFn

/-!
# Word encodings and table selection

Words use least-significant-bit-first coordinates. Sorting uses its own
lexicographic key order; equality of state keys is independent of bit order.
Table selection is charged for all selected output bits.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n k w R : ℕ}

/-- Assemble a word from its coordinate bits. -/
def word (bits : Fin w → Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast (by simp)

@[simp] theorem word_bit (bits : Fin w → Bool) (i : Fin w) :
    (word bits).getLsbD i.val = bits i := by
  rw [word, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  simp

@[simp] theorem word_getElem (bits : Fin w → Bool) (i : ℕ) (hi : i < w) :
    (word bits)[i] = bits ⟨i, hi⟩ := word_bit bits ⟨i, hi⟩

@[simp] theorem word_bits (a : BitVec w) : word (fun i : Fin w => a.getLsbD i.val) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact word_bit _ ⟨i, hi⟩

/-- Coordinate functions representing a word-valued function. -/
def wordWires (a : (Fin n → Bool) → BitVec w) : Set ((Fin n → Bool) → Bool) :=
  Set.range fun i : Fin w => fun x => (a x).getLsbD i.val

/-- Testing a word against a constant needs only literal tests and a conjunction. -/
theorem synthesis_word_eq_const (s : Set ((Fin n → Bool) → Bool))
    (a : (Fin n → Bool) → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ s) (v : BitVec k) :
    Synthesis Boolean.interpretation s {fun x => decide (a x = v)} (2 * k + 1) := by
  have hlit (i : Fin k) : Synthesis Boolean.interpretation s
      {fun x => decide ((a x).getLsbD i.val = v.getLsbD i.val)} 1 := by
    have h := Synthesis.of_mem (I := Boolean.interpretation) (ha i)
    cases hv : v.getLsbD i.val
    · simpa only [hv, Bool.decide_eq_false] using h.not
    · simpa only [hv, Bool.decide_eq_true] using
        h.mono Set.Subset.rfl Set.Subset.rfl (by lia : 0 ≤ 1)
  have h := Synthesis.forall_mem (s := s) Finset.univ
    (fun i : Fin k => fun x => decide ((a x).getLsbD i.val = v.getLsbD i.val))
    (fun _ => 1) (fun i _ => hlit i)
  have heq (x : Fin n → Bool) : (∀ i : Fin k, (a x).getLsbD i.val = v.getLsbD i.val) ↔ a x = v :=
    ⟨fun h => BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i, hi⟩),
      fun h i => congrArg (fun a => a.getLsbD i.val) h⟩
  simpa only [Finset.mem_univ, forall_true_left, decide_eq_true_eq, heq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

/-- Select a record by its binary index, returning zero if no index matches. -/
def selectBits (index : BitVec k) (values : Fin R → Fin w → Bool) : Fin w → Bool :=
  fun bit => decide (∃ j : Fin R, index = BitVec.ofNat k j.val ∧ values j bit = true)

/-- Bounded indices have distinct encodings. -/
theorem ofNat_index_injective (hR : R ≤ 2 ^ k) :
    Function.Injective (fun j : Fin R => BitVec.ofNat k j.val) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg BitVec.toNat hij
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (i.isLt.trans_le hR),
    Nat.mod_eq_of_lt (j.isLt.trans_le hR)] using h

/-- On an in-range index, the selector returns exactly the corresponding record. -/
theorem selectBits_eq (hR : R ≤ 2 ^ k) (values : Fin R → Fin w → Bool) (j : Fin R) :
    selectBits (BitVec.ofNat k j.val) values = values j := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  simp [selectBits, (ofNat_index_injective hR).eq_iff]

/-- Select among already available records, charging comparisons and every output bit. -/
theorem synthesis_selectBits (s : Set ((Fin n → Bool) → Bool))
    (index : (Fin n → Bool) → BitVec k) (values : Fin R → (Fin n → Bool) → Fin w → Bool)
    (hi : ∀ i : Fin k, (fun x => (index x).getLsbD i.val) ∈ s)
    (hv : ∀ j bit, (fun x => values j x bit) ∈ s) :
    Synthesis Boolean.interpretation s
      (Set.range fun bit x => selectBits (index x) (fun j => values j x) bit)
      (w * (R * (2 * k + 3) + 1)) := by
  have hs := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun bit x => selectBits (index x) (fun j => values j x) bit)
    (fun _ => R * (2 * k + 3) + 1) (fun bit => ?_)
  · simpa using hs
  · have h := Synthesis.exists_mem (s := s) Finset.univ
      (fun j : Fin R => fun x => decide (index x = BitVec.ofNat k j.val) && values j x bit)
      (fun _ => 2 * k + 2) (fun j _ => ?_)
    · simpa [selectBits, Nat.add_assoc] using h
    · exact (synthesis_word_eq_const s index hi _).and (Synthesis.of_mem (hv j bit))

end IteratedFunctions
