/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Detector
import Mathlib.Tactic.Linarith

/-! # Boolean circuits for collision detection and record selection -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Algebraic.MassProduction.Sorting
open Algebraic.MassProduction.Sorting.Semantics

variable {n w R : ℕ}

def wires {m : ℕ} (a : State n → Fin m → Bool) : Set (State n → Bool) :=
  Set.range fun i x => a x i

theorem synthesis_bits_eq {m : ℕ} (s : Set (State n → Bool))
    (a b : State n → Fin m → Bool) (ha : wires a ⊆ s) (hb : wires b ⊆ s) :
    Synthesis Boolean.interpretation s {fun x => decide (a x = b x)} (6 * m + 1) := by
  have h := synthesis_word_eq s (fun x => word (a x)) (fun x => word (b x))
    (fun i => by simpa using ha ⟨i, rfl⟩) (fun i => by simpa using hb ⟨i, rfl⟩)
  have he (x : State n) : word (a x) = word (b x) ↔ a x = b x := by
    constructor
    · intro h; funext i
      simpa using congrArg (fun v : BitVec m => v.getLsbD i.val) h
    · exact congrArg word
  simpa only [he] using h

theorem synthesis_bits_mux {m : ℕ} (s : Set (State n → Bool))
    (a b : State n → Fin m → Bool) (flag : State n → Bool)
    (ha : wires a ⊆ s) (hb : wires b ⊆ s) (hf : flag ∈ s) :
    Synthesis Boolean.interpretation s (wires fun x => if flag x then a x else b x)
      (4 * m) := by
  have h := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun i x => if flag x then a x i else b x i) (fun _ => 4)
    (fun i => Synthesis.mux hf (ha ⟨i, rfl⟩) (hb ⟨i, rfl⟩))
  simpa only [wires, ite_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

namespace Record

def wireSet (a : State n → Record n w) := wires fun x => encode (a x)

theorem padding_mem (s : Set (State n → Bool)) (a : State n → Record n w)
    (ha : wireSet a ⊆ s) : (fun x => (a x).padding) ∈ s := by
  have h := ha ⟨Fin.castAdd (w + n + 1) 0, rfl⟩
  simpa [encode] using h

theorem state_mem (s : Set (State n → Bool)) (a : State n → Record n w)
    (ha : wireSet a ⊆ s) (i : Fin n) : (fun x => (a x).state i) ∈ s := by
  have h := ha ⟨Fin.castAdd (w + n + 1) i.succ, rfl⟩
  simpa [encode] using h

theorem checkpoint_mem (s : Set (State n → Bool)) (a : State n → Record n w)
    (ha : wireSet a ⊆ s) : (fun x => (a x).checkpoint) ∈ s := by
  have h := ha ⟨Fin.natAdd (n + 1) 0, rfl⟩
  simpa [encode] using h

theorem index_mem (s : Set (State n → Bool)) (a : State n → Record n w)
    (ha : wireSet a ⊆ s) (i : Fin w) : (fun x => (a x).index.getLsbD i.val) ∈ s := by
  have h := ha ⟨Fin.natAdd (n + 1) (Fin.castAdd n i).succ, rfl⟩
  simpa [encode] using h

theorem payload_mem (s : Set (State n → Bool)) (a : State n → Record n w)
    (ha : wireSet a ⊆ s) (i : Fin n) : (fun x => (a x).payload i) ∈ s := by
  have h := ha ⟨Fin.natAdd (n + 1) (Fin.natAdd w i).succ, rfl⟩
  simpa [encode] using h

theorem synthesis_collision (s : Set (State n → Bool)) (a b : State n → Record n w)
    (ha : wireSet a ⊆ s) (hb : wireSet b ⊆ s) :
    Synthesis Boolean.interpretation s {fun x => collision (a x) (b x)}
      (20 * (width n w + 1)) := by
  have hs := synthesis_bits_eq s (fun x => (a x).state) (fun x => (b x).state)
    (by rintro _ ⟨i, rfl⟩; exact state_mem s a ha i)
    (by rintro _ ⟨i, rfl⟩; exact state_mem s b hb i)
  have he := synthesis_bits_eq s (fun x => encode (a x)) (fun x => encode (b x)) ha hb
  have hne : Synthesis Boolean.interpretation s {fun x => decide (a x ≠ b x)}
      (6 * width n w + 1 + 1) := by
    simpa only [encode_injective.eq_iff, decide_not] using he.not
  have h := (((Synthesis.of_mem (padding_mem s a ha)).not.and
    (Synthesis.of_mem (padding_mem s b hb)).not).and hs).and hne
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by unfold width; lia)

def pairEncode (pair : Record n w × Record n w) : Fin (width n w + width n w) → Bool :=
  Fin.append (encode pair.1) (encode pair.2)

def pairWires (p : State n → Record n w × Record n w) := wires fun x => pairEncode (p x)

theorem pair_left (p : State n → Record n w × Record n w) :
    wireSet (fun x => (p x).1) ⊆ pairWires p := by
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castAdd (width n w) i, by simp [pairEncode]⟩

theorem pair_right (p : State n → Record n w × Record n w) :
    wireSet (fun x => (p x).2) ⊆ pairWires p := by
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.natAdd (width n w) i, by simp [pairEncode]⟩

theorem synthesis_detect (s : Set (State n → Bool)) (records : State n → Fin R → Record n w)
    (hr : ∀ j, wireSet (fun x => records x j) ⊆ s)
    (hconst : ∀ b : Bool, (fun _ : State n => b) ∈ s) :
    Synthesis Boolean.interpretation s (pairWires fun x => detect (records x))
      (30 * R * (width n w + 1)) := by
  let flags := fun (j : Fin (R - 1)) x =>
    collision (adjacentPair (records x) j).1 (adjacentPair (records x) j).2
  have hf := Synthesis.family (I := Boolean.interpretation) (s := s) flags
    (fun _ => 20 * (width n w + 1)) (fun j => synthesis_collision s _ _ (hr _) (hr _))
  have hs := synthesis_chooseRecord (s ∪ Set.range flags)
    (fun x j => flags j x) (fun x j => pairEncode (adjacentPair (records x) j))
    (fun _ => pairEncode (pad, pad)) (fun j => Or.inr ⟨j, rfl⟩) (fun j bit => ?_)
    (fun bit => Or.inl (hconst _))
  · have h := hf.trans hs
    have he : (pairWires fun x => detect (records x)) =
        (Set.range fun bit x => chooseRecord (fun j => flags j x)
          (fun j => pairEncode (adjacentPair (records x) j)) (pairEncode (pad, pad))
          (R - 1) bit) := by
      unfold pairWires wires detect
      congr 1
      funext bit x
      exact congrFun (chooseRecord_map pairEncode (fun j => flags j x)
        (adjacentPair (records x)) (pad, pad) (R - 1)) bit
    rw [he]
    apply h.mono Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    nlinarith [Nat.sub_le R 1, Nat.mul_le_mul_right (width n w + 1) (Nat.sub_le R 1)]
  · induction bit using Fin.addCases with
    | left bit =>
      exact Or.inl (by
        simpa only [pairEncode, Fin.append_left, Fin.append_right, adjacentPair]
          using hr _ ⟨bit, rfl⟩)
    | right bit =>
      exact Or.inl (by
        simpa only [pairEncode, Fin.append_left, Fin.append_right, adjacentPair]
          using hr _ ⟨bit, rfl⟩)

end Record
end IteratedFunctions
