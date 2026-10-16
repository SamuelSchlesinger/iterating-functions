/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ForestNavigation
public import Proofs.NavigationFeatures

/-! # Encoded forest records and shared dictionary synthesis -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n a M Q v : ℕ}

/-- A lookup result keeps each query's success flag and its payload wires together. -/
def dictionaryWires (flags : State a → Fin Q → Bool)
    (values : State a → Fin Q → State v) : Set (State a → Bool) :=
  (Set.range fun j z => flags z j) ∪ ⋃ j, wires (fun z => values z j)

def dictionaryCost (n v M Q : ℕ) : ℕ :=
  256 * (M + Q + 1) * (Nat.clog 2 (M + Q + 1) + n + (1 + v) + 3) ^ 3

/-- Apply the shared dictionary to already available query rows. -/
theorem synthesis_dictionary_rows (s : Set (State a → Bool))
    (keys : Fin M → State n) (values : Fin M → State v) (hk : Function.Injective keys)
    (queries : State a → Fin Q → State n)
    (hq : ∀ j, wires (fun z => queries z j) ⊆ s) :
    ∃ flags : State a → Fin Q → Bool, ∃ records : State a → Fin Q → State v,
      (∀ z j, flags z j = true ↔ ∃ i, keys i = queries z j) ∧
      (∀ z j i, keys i = queries z j → records z j = values i) ∧
      Synthesis Boolean.interpretation s (dictionaryWires flags records)
        (dictionaryCost n v M Q) := by
  let packed : State a → State (Q * n) := fun z bit =>
    let ij := (finProdFinEquiv (m := Q) (n := n)).symm bit
    queries z ij.1 ij.2
  have hpacked (z : State a) (j : Fin Q) :
      (fun bit => packed z (finProdFinEquiv (j, bit))) = queries z j := by
    funext bit
    simp only [packed, Equiv.symm_apply_apply]
  obtain ⟨lookup, hf, hv, _, hs⟩ := SharedLookup.fixed_dictionary (Q := Q) keys values hk
  let result := fun z => lookup.eval Boolean.interpretation (packed z)
  let flags := fun z j => result z (finProdFinEquiv (j, (0 : Fin (1 + v))))
  let records := fun z j bit => result z (finProdFinEquiv (j, Fin.natAdd 1 bit))
  refine ⟨flags, records, fun z j => ?_, fun z j i hi => ?_, ?_⟩
  · simpa only [hpacked] using hf (packed z) j
  · funext bit
    exact hv (packed z) j i (by rwa [hpacked]) bit
  · have h := Synthesis.circuit (I := Boolean.interpretation) (s := s) lookup packed
      (fun bit => hq _ ⟨_, rfl⟩)
    apply h.mono Set.Subset.rfl _ hs
    rintro _ (⟨j, rfl⟩ | hh)
    · exact ⟨_, rfl⟩
    · obtain ⟨j, bit, rfl⟩ := Set.mem_iUnion.mp hh
      exact ⟨_, rfl⟩

/-- OR all available flags, including the empty-family case. -/
theorem synthesis_any_flags (s : Set (State a → Bool)) (flags : State a → Fin Q → Bool)
    (hf : ∀ j, (fun z => flags z j) ∈ s) :
    Synthesis Boolean.interpretation s {fun z => decide (∃ j, flags z j = true)} (Q + 1) := by
  simpa using Synthesis.exists_mem (s := s) Finset.univ (fun j z => flags z j)
    (fun _ => 0) (fun j _ => Synthesis.of_mem (hf j))

/-- A full finite orbit prefix, with its state rows individually addressable. -/
def orbitPrefixWires (f : State n → State n) (x : State a → State n) (K : ℕ) :
    Set (State a → Bool) := ⋃ j : Fin (K + 1), wires (fun z => f^[j.val] (x z))

theorem synthesis_prefix (c : Circuit Boolean.signature n n) (s : Set (State a → Bool))
    (x : State a → State n) (hx : wires x ⊆ s) (K : ℕ) :
    Synthesis Boolean.interpretation s (orbitPrefixWires (c.eval Boolean.interpretation) x K)
      (K * c.size) := by
  apply (synthesis_orbit Boolean.interpretation c s x (fun bit => hx ⟨bit, rfl⟩) K).mono
    Set.Subset.rfl _ le_rfl
  intro bit hbit
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hbit
  exact Set.mem_iUnion.mpr ⟨j.val, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr j.isLt, hj⟩⟩

/-- Detect a target in a prefix without pairwise comparisons among prefix states. -/
theorem synthesis_prefix_hit (s : Set (State a → Bool)) (trace : State a → Fin Q → State n)
    (y : State a → State n) (ht : ∀ j, wires (fun z => trace z j) ⊆ s) (hy : wires y ⊆ s) :
    Synthesis Boolean.interpretation s {fun z => decide (∃ j, trace z j = y z)}
      (Q * (6 * n + 2) + 1) := by
  simpa using Synthesis.exists_mem (s := s) Finset.univ
    (fun j z => decide (trace z j = y z)) (fun _ => 6 * n + 1)
    (fun j _ => synthesis_bits_eq s (fun z => trace z j) y (ht j) hy)

/-- Multiplex whole state records using a shared flag. -/
theorem synthesis_record_mux (s : Set (State a → Bool)) (flag : State a → Bool)
    (x y : State a → State v) (hf : flag ∈ s) (hx : wires x ⊆ s) (hy : wires y ⊆ s) :
    Synthesis Boolean.interpretation s (wires (fun z => if flag z then x z else y z))
      (4 * v) := by
  have h := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun bit z => if flag z then x z bit else y z bit) (fun _ => 4)
    (fun bit => Synthesis.mux hf (hx ⟨bit, rfl⟩) (hy ⟨bit, rfl⟩))
  simpa only [wires, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, Nat.mul_comm, ite_apply] using h

abbrev forestRecordWidth (n : ℕ) := n + ((n + 3) + ((n + 3) + (n + 3)))

/-- Original state, depth, and inclusive subtree interval. -/
noncomputable def forestRecord (f : State n → State n)
    (low high : State n → Fin (Nat.card (State n))) (x : State n) : State (forestRecordWidth n) :=
  Fin.append x (Fin.append (fun bit => (depthWord f x).getLsbD bit.val)
    (Fin.append (fun bit => (BitVec.ofNat (n + 3) (low x).val).getLsbD bit.val)
      (fun bit => (BitVec.ofNat (n + 3) (high x).val).getLsbD bit.val)))

def forestRecordState (r : State (forestRecordWidth n)) : State n :=
  fun bit => r (Fin.castAdd ((n + 3) + ((n + 3) + (n + 3))) bit)

def forestRecordDepth (r : State (forestRecordWidth n)) : BitVec (n + 3) :=
  word fun bit => r (Fin.natAdd n (Fin.castAdd ((n + 3) + (n + 3)) bit))

def forestRecordLow (r : State (forestRecordWidth n)) : BitVec (n + 3) :=
  word fun bit => r (Fin.natAdd n (Fin.natAdd (n + 3) (Fin.castAdd (n + 3) bit)))

def forestRecordHigh (r : State (forestRecordWidth n)) : BitVec (n + 3) :=
  word fun bit => r (Fin.natAdd n (Fin.natAdd (n + 3) (Fin.natAdd (n + 3) bit)))

theorem forestRecord_fields (s : Set (State a → Bool))
    (r : State a → State (forestRecordWidth n)) (hr : wires r ⊆ s) :
    wires (fun z => forestRecordState (r z)) ⊆ s ∧
      wordWires (fun z => forestRecordDepth (r z)) ⊆ s ∧
      wordWires (fun z => forestRecordLow (r z)) ⊆ s ∧
      wordWires (fun z => forestRecordHigh (r z)) ⊆ s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨bit, rfl⟩
    exact hr ⟨_, rfl⟩
  · rintro _ ⟨bit, rfl⟩
    simp only [forestRecordDepth, word_bit]
    exact hr ⟨_, rfl⟩
  · rintro _ ⟨bit, rfl⟩
    simp only [forestRecordLow, word_bit]
    exact hr ⟨_, rfl⟩
  · rintro _ ⟨bit, rfl⟩
    simp only [forestRecordHigh, word_bit]
    exact hr ⟨_, rfl⟩

@[simp] theorem forestRecordState_record (f : State n → State n)
    (low high : State n → Fin (Nat.card (State n))) (x : State n) :
    forestRecordState (forestRecord f low high x) = x := by
  funext bit
  simp only [forestRecordState, forestRecord, Fin.append_left]

@[simp] theorem forestRecordDepth_record (f : State n → State n)
    (low high : State n → Fin (Nat.card (State n))) (x : State n) :
    forestRecordDepth (forestRecord f low high x) = depthWord f x := by
  simp only [forestRecordDepth, forestRecord, Fin.append_left, Fin.append_right, word_bits]

@[simp] theorem forestRecordLow_record (f : State n → State n)
    (low high : State n → Fin (Nat.card (State n))) (x : State n) :
    (forestRecordLow (forestRecord f low high x)).toNat = (low x).val := by
  simp only [forestRecordLow, forestRecord, Fin.append_left, Fin.append_right, word_bits]
  apply Nat.mod_eq_of_lt
  have hh := (low x).isLt
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool] at hh
  exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by lia))

@[simp] theorem forestRecordHigh_record (f : State n → State n)
    (low high : State n → Fin (Nat.card (State n))) (x : State n) :
    (forestRecordHigh (forestRecord f low high x)).toNat = (high x).val := by
  simp only [forestRecordHigh, forestRecord, Fin.append_right, word_bits]
  apply Nat.mod_eq_of_lt
  have hh := (high x).isLt
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool] at hh
  exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by lia))

end IteratedFunctions
