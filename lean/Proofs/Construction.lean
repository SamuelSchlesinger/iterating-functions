/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.DecoderCircuits
import Mathlib.Tactic.Linarith

/-! # Assembling the fixed-power circuit -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Algebraic.MassProduction.Sorting
open Algebraic.MassProduction.Sorting.Semantics

variable {n w M R : ℕ}

namespace Record

def recordsWires (records : State n → Fin R → Record n w) : Set (State n → Bool) :=
  ⋃ j, wireSet (fun x => records x j)

theorem records_mem (records : State n → Fin R → Record n w) (j : Fin R) :
    wireSet (fun x => records x j) ⊆ recordsWires records :=
  Set.subset_iUnion_of_subset j Set.Subset.rfl

theorem initial_available (s : Set (State n → Bool)) (f : State n → State n)
    (T K : ℕ) (cp : Fin M → State n) (hp : prefixWires f K ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State n => b) ∈ s) :
    recordsWires (fun x => initial (R := R) (w := w) f T K cp x) ⊆ s := by
  intro fn hfn
  obtain ⟨j, bit, rfl⟩ := Set.mem_iUnion.mp hfn
  dsimp only [initial]
  split_ifs with h1 h2
  · exact hc _
  · induction bit using Fin.addCases with
    | left bit =>
      induction bit using Fin.cases with
      | zero => exact hc false
      | succ bit => simpa [encode, query] using hp (prefix_mem f h2 bit)
    | right bit =>
      simp only [encode, query, Fin.append_right]
      exact hc _
  · exact hc _

theorem synthesis_sorted (s : Set (State n → Bool)) (d : ℕ)
    (records : State n → Fin (networkRecords d) → Record n w)
    (hr : recordsWires records ⊆ s) :
    Synthesis Boolean.interpretation s (recordsWires fun x => sorted d (records x))
      (18 * d ^ 2 * 2 ^ d * (width n w + 1)) := by
  have h := Synthesis.circuit (I := Boolean.interpretation) (s := s)
    (SharedSorting.sort (keyFits (n := n) (w := w)) d true) (fun x => pack (records x))
    (fun bit => hr (records_mem records _ ⟨_, rfl⟩))
  apply h.mono Set.Subset.rfl ?_ (SharedSorting.sort_size _ _ _)
  intro fn hfn
  obtain ⟨j, bit, rfl⟩ := Set.mem_iUnion.mp hfn
  refine ⟨finProdFinEquiv (j, bit), ?_⟩
  funext x
  simp only [sorted, encode_decode, flatRecords, networkRecord]
  exact congrFun (SharedSorting.sort_eval _ _ _ _) _

end Record

noncomputable def fixedOutput (c : Circuit Boolean.signature n n) (T K d : ℕ)
    (cp : Fin M → State n) (x : State n) : State n :=
  let pair := Record.detect (Record.sorted d (Record.initial (w := w)
    (c.eval Boolean.interpretation) T K cp x))
  reconstruct (c.eval Boolean.interpretation) T K x pair.1 pair.2

theorem exists_fixedOutput (c : Circuit Boolean.signature n n) (T K d : ℕ)
    (cp : Fin M → State n) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation (fixedOutput (w := w) c T K d cp) ∧
      out.size ≤ 2 + 5 * K * c.size +
        (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n w + 1) +
        1000 * (K + 1) * (n + w + 1) ^ 2 := by
  let f := c.eval Boolean.interpretation
  let constants : Set (State n → Bool) := {fun _ => false, fun _ => true}
  have hconst : Synthesis Boolean.interpretation (inputs n) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let s := inputs n ∪ constants
  have hc (b : Bool) : (fun _ : State n => b) ∈ s := by cases b <;> simp [s, constants]
  have hp := synthesis_orbit Boolean.interpretation c s id
    (fun bit => Or.inl ⟨bit, rfl⟩) K
  let records := fun x => Record.initial (R := networkRecords d) (w := w) f T K cp x
  let sorted := fun x => Record.sorted d (records x)
  let pair := fun x => Record.detect (sorted x)
  let s1 := s ∪ prefixWires f K
  have hs := Record.synthesis_sorted s1 d records
    (Record.initial_available s1 f T K cp (fun _ h => Or.inr h) (fun b => Or.inl (hc b)))
  let s2 := s1 ∪ Record.recordsWires sorted
  have hd := Record.synthesis_detect s2 sorted
    (fun j _ h => Or.inr (Record.records_mem sorted j h)) (fun b => Or.inl (Or.inl (hc b)))
  let s3 := s2 ∪ Record.pairWires pair
  have hout := synthesis_reconstruct s3 c T K (fun x => (pair x).1) (fun x => (pair x).2)
    (fun _ h => Or.inr (Record.pair_left pair h))
    (fun _ h => Or.inr (Record.pair_right pair h))
    (fun _ h => Or.inl (Or.inl (Or.inr h)))
    (fun b => Or.inl (Or.inl (Or.inl (hc b))))
  have h := hconst.trans (hp.trans (hs.trans (hd.trans hout)))
  have hfinal : Synthesis Boolean.interpretation (inputs n)
      (wires (fixedOutput (w := w) c T K d cp))
      (2 + 5 * K * c.size + (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n w + 1) +
        1000 * (K + 1) * (n + w + 1) ^ 2) := by
    apply h.mono Set.Subset.rfl Set.Subset.rfl
    rw [networkRecords_eq_two_pow]
    ring_nf
    exact le_rfl
  exact hfinal.exists_circuit_outputs

end IteratedFunctions
