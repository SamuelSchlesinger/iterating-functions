/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Synthesis
public import Complexitylib.Algebraic.MassProduction.SortingCorrectness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Sorting with shared comparisons

The semantic sorter and its correctness proof are from Samuel Schlesinger's
circuit library. This implementation shares one linear-size comparison across
all bits of the two records. Thus a comparator uses `O(recordWidth)` gates,
and a depth-`d` Batcher network uses `O(d² 2^d recordWidth)` gates.
-/

@[expose] public section

namespace IteratedFunctions.SharedSorting

open Cslib.Circuits Algebraic.MassProduction.Sorting

variable {k r : ℕ}

private theorem compareSwapBits_apply (h : k ≤ r)
    (x : Fin (2 * r) → Bool) (o : Fin (2 * r)) :
    compareSwapBits h x o =
      if compareSwapFlag h x then x (reverseRecordPairOutput o) else x o := by
  obtain ⟨⟨side, bit⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := r)).surjective o
  unfold compareSwapBits reverseRecordPairOutput
  simp only [Equiv.symm_apply_apply]
  cases compareSwapFlag h x <;> simp only [Bool.false_eq_true, ↓reduceIte]
  induction side using Fin.cases with
  | zero => simp [recordPairSide]
  | succ side => simp [recordPairSide]

/-- A complete compare--exchange with one shared comparison. -/
theorem exists_comparator (h : k ≤ r) :
    ∃ c : Circuit Boolean.signature (2 * r) (2 * r),
      c.Computes Boolean.interpretation (compareSwapBits h) ∧
      c.size ≤ 9 * k + 1 + 8 * r := by
  let flag := fun x : Fin (2 * r) → Bool => compareSwapFlag h x
  have hcmp : Synthesis Boolean.interpretation (inputs (2 * r)) {flag} (9 * k + 1) := by
    have hc := synthesis_lexLess (inputs (2 * r))
      (fun x => recordKey h x 1) (fun x => recordKey h x 0)
      (fun i => ⟨recordPairIndex 1 (Fin.castLE h i), rfl⟩)
      (fun i => ⟨recordPairIndex 0 (Fin.castLE h i), rfl⟩)
    have heq : (fun x => lexLess (recordKey h x 1) (recordKey h x 0)) = flag := by
      funext x
      exact Bool.eq_iff_iff.mpr ((lexLess_eq_true_iff _ _).trans
        (compareSwapFlag_eq_true_iff h x).symm)
    simpa only [heq] using hc
  have houtputs : Synthesis Boolean.interpretation (inputs (2 * r) ∪ {flag})
      (Set.range fun o x => compareSwapBits h x o) (8 * r) := by
    have hs := Synthesis.family (I := Boolean.interpretation)
      (s := inputs (2 * r) ∪ {flag})
      (fun o x => compareSwapBits h x o) (fun _ => 4) (fun o => ?_)
    · simpa [Nat.mul_comm, Nat.mul_assoc] using hs
    · have hm := Synthesis.mux (s := inputs (2 * r) ∪ {flag})
        (f := flag) (a := fun x => x (reverseRecordPairOutput o)) (b := fun x => x o)
        (by simp) (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩)
      simpa only [compareSwapBits_apply, flag] using hm
  exact (hcmp.trans houtputs).exists_circuit_outputs

/-- A chosen comparator; choice affects syntax only, not semantics or the certified bound. -/
noncomputable def comparator (h : k ≤ r) : Circuit Boolean.signature (2 * r) (2 * r) :=
  (exists_comparator h).choose

theorem comparator_eval (h : k ≤ r) (x : Fin (2 * r) → Bool) :
    (comparator h).eval Boolean.interpretation x = compareSwapBits h x :=
  (exists_comparator h).choose_spec.1 x

theorem comparator_size (h : k ≤ r) : (comparator h).size ≤ 18 * (r + 1) := by
  have := (exists_comparator h).choose_spec.2
  change (comparator h).size ≤ 9 * k + 1 + 8 * r at this
  lia

noncomputable def pair (h : k ≤ r) (ascending : Bool) :=
  if ascending then comparator h else (comparator h).mapOutputs reverseRecordPairOutput

theorem pair_eval (h : k ≤ r) (ascending : Bool) (x : Fin (2 * r) → Bool) :
    (pair h ascending).eval Boolean.interpretation x = comparePairBits h ascending x := by
  cases ascending <;> simp [pair, comparePairBits, comparator_eval]

@[simp] theorem pair_size (h : k ≤ r) (ascending : Bool) :
    (pair h ascending).size = (comparator h).size := by
  cases ascending <;> simp [pair]

noncomputable def layer (d : ℕ) (h : k ≤ r) (ascending : Bool) :=
  (Circuit.parallelFinVector (networkRecords d) (2 * r)
    (fun i => (pair h ascending).mapInputs (gatherLayerPairInput d r i))).mapOutputs
      (compareLayerOutputMap d r)

theorem layer_eval (d : ℕ) (h : k ≤ r) (ascending : Bool)
    (x : Fin (networkBits (d + 1) r) → Bool) :
    (layer d h ascending).eval Boolean.interpretation x = compareLayerBits d h ascending x := by
  funext o
  simp only [layer, Circuit.eval_mapOutputs, Function.comp_apply, compareLayerOutputMap,
    compareLayerBits]
  split <;> rw [Circuit.eval_parallelFinVector, Circuit.eval_mapInputs, pair_eval]

@[simp] theorem layer_size (d : ℕ) (h : k ≤ r) (ascending : Bool) :
    (layer d h ascending).size = networkRecords d * (comparator h).size := by
  simp [layer]

noncomputable def merge (h : k ≤ r) : (d : ℕ) → Bool →
    Circuit Boolean.signature (networkBits d r) (networkBits d r)
  | 0, _ => Circuit.id _ (networkBits 0 r)
  | d + 1, ascending =>
    (Circuit.parallelHalves (merge h d ascending) (merge h d ascending)).comp (layer d h ascending)

noncomputable def sort (h : k ≤ r) : (d : ℕ) → Bool →
    Circuit Boolean.signature (networkBits d r) (networkBits d r)
  | 0, _ => Circuit.id _ (networkBits 0 r)
  | d + 1, ascending =>
    (merge h (d + 1) ascending).comp
      (Circuit.parallelHalves (sort h d true) (sort h d false))

theorem merge_eval (h : k ≤ r) (d : ℕ) (ascending : Bool)
    (x : Fin (networkBits d r) → Bool) :
    (merge h d ascending).eval Boolean.interpretation x = bitonicMergeBits h d ascending x := by
  induction d generalizing ascending with
  | zero => rfl
  | succ d ih =>
    rw [merge, Circuit.eval_comp, Circuit.eval_parallelHalves, layer_eval, ih, ih]
    rfl

theorem sort_eval (h : k ≤ r) (d : ℕ) (ascending : Bool)
    (x : Fin (networkBits d r) → Bool) :
    (sort h d ascending).eval Boolean.interpretation x = bitonicSortBits h d ascending x := by
  induction d generalizing ascending with
  | zero => rfl
  | succ d ih =>
    rw [sort, Circuit.eval_comp, Circuit.eval_parallelHalves, merge_eval, ih, ih]
    rfl

theorem merge_size (h : k ≤ r) (d : ℕ) (ascending : Bool) :
    (merge h d ascending).size ≤ d * networkRecords d * (comparator h).size := by
  induction d with
  | zero => simp [merge]
  | succ d ih =>
    simp only [merge, Circuit.size_comp, Circuit.size_parallelHalves, layer_size,
      networkRecords_succ]
    nlinarith

/-- The sorter has the record-linear, squared-logarithmic gate bound. -/
theorem sort_size (h : k ≤ r) (d : ℕ) (ascending : Bool) :
    (sort h d ascending).size ≤ 18 * d ^ 2 * 2 ^ d * (r + 1) := by
  suffices hs : (sort h d ascending).size ≤ d ^ 2 * networkRecords d * (comparator h).size by
    calc
      _ ≤ d ^ 2 * networkRecords d * (18 * (r + 1)) :=
        hs.trans (Nat.mul_le_mul_left _ (comparator_size h))
      _ = _ := by rw [networkRecords_eq_two_pow]; ring
  induction d generalizing ascending with
  | zero => simp [sort]
  | succ d ih =>
    have hm := merge_size h (d + 1) ascending
    have ht := ih true
    have hf := ih false
    simp only [sort, Circuit.size_comp, Circuit.size_parallelHalves]
    rw [networkRecords_succ] at hm ⊢
    nlinarith [Nat.zero_le (d * d * networkRecords d * (comparator h).size)]

/-- The optimized circuit inherits both sortedness and preservation of complete records. -/
theorem sort_correct (h : k ≤ r) (d : ℕ) (ascending : Bool)
    (x : Fin (networkBits d r) → Bool) :
    FlatKeysSorted h ascending ((sort h d ascending).eval Boolean.interpretation x) ∧
      FlatRecordsPermute ((sort h d ascending).eval Boolean.interpretation x) x := by
  rw [sort_eval]
  exact ⟨bitonicSortBits_keysSorted h d ascending x,
    bitonicSortBits_recordsPermute h d ascending x⟩

end IteratedFunctions.SharedSorting
