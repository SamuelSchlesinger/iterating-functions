/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.VisitSchedules
public import Proofs.VisitCounts
public import Proofs.NavigationCircuits

/-! # Circuits returning complete visit schedules -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n : ℕ}
noncomputable local instance visitScheduleStateOrder : LinearOrder (State n) := stateOrder n

/-- Minimal return period, with zero denoting a noncyclic state. -/
theorem minimal_period_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n (n + 1),
      (∀ x, (word (out.eval Boolean.interpretation x)).toNat =
        Function.minimalPeriod (c.eval Boolean.interpretation) x) ∧
      out.size ≤ 11000000 * powerBudget n c.size (2 ^ n) L := by
  let f := c.eval Boolean.interpretation
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  obtain ⟨cyclic, hc, hcs⟩ := cyclicity_circuit c L hL hLN
  let src := inputs n ∪ {fun _ : State n => false}
  have hlabels := Synthesis.circuit (I := Boolean.interpretation) (s := src) labels id
    (fun bit => Or.inl ⟨bit, rfl⟩)
  have hcyclic := Synthesis.circuit (I := Boolean.interpretation) (s := src) cyclic id
    (fun bit => Or.inl ⟨bit, rfl⟩)
  let s1 := src ∪ (wires (labels.eval Boolean.interpretation) ∪
    wires (cyclic.eval Boolean.interpretation))
  let ell := fun x => labelLength (labels.eval Boolean.interpretation x)
  have he : wordWires ell ⊆ s1 := by
    rintro _ ⟨bit, rfl⟩
    simp only [ell, labelLength, word_bit]
    exact Or.inr (Or.inl ⟨_, rfl⟩)
  have hw := resize_wires (v := n + 1) s1 ell he (Or.inl (Or.inr rfl))
  have hmux := synthesis_word_mux s1 (fun x => (ell x).setWidth (n + 1))
    (fun _ => (0 : BitVec (n + 1))) (fun x => cyclic.eval Boolean.interpretation x 0)
    (Or.inr (Or.inr ⟨0, rfl⟩)) (fun i => hw ⟨i, rfl⟩)
    (fun i => by simpa using (show (fun _ : State n => false) ∈ s1 from Or.inl (Or.inr rfl)))
  obtain ⟨out, ho, hs⟩ := ((Synthesis.const (s := inputs n) false).trans
    ((hlabels.union hcyclic).trans hmux)).exists_circuit_outputs
  refine ⟨out, fun x => ?_, hs.trans ?_⟩
  · rw [ho x, word_bits]
    by_cases hy : x ∈ Function.periodicPts f
    · have htrue := (hc x).mpr hy
      simp only [htrue, ite_true]
      have hμ := (transientDepth_eq_zero_iff f x).mpr hy
      have hperiod : cycleLength f x = Function.minimalPeriod f x := by
        simp only [cycleLength, hμ, Function.iterate_zero_apply]
      have hbound : cycleLength f x < 2 ^ (n + 1) :=
        (cycleLength_le_states f x).trans_lt (Nat.pow_lt_pow_right (by decide) (by lia))
      dsimp only [ell]
      simp only [hl x, canonicalLabel, labelLength_bits, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat]
      change cycleLength f x % 2 ^ (n + 3) % 2 ^ (n + 1) = Function.minimalPeriod f x
      rw [Nat.mod_eq_of_lt (label_number_bounds f x).1, Nat.mod_eq_of_lt hbound]
      exact hperiod
    · have hfalse : cyclic.eval Boolean.interpretation x 0 = false :=
        Bool.eq_false_iff.mpr (fun h => hy ((hc x).mp h))
      simp only [hfalse, Bool.false_eq_true, ite_false]
      exact (Function.minimalPeriod_eq_zero_of_notMem_periodicPts hy).symm
  · have hb : n + 1 ≤ powerBudget n c.size (2 ^ n) L := by
      have hh := Nat.mul_le_mul_left ((n + 1) ^ 3)
        (show 1 ≤ L + 2 ^ n / L + 1 by lia)
      unfold powerBudget
      nlinarith [Nat.zero_le (n ^ 3)]
    lia

/-- One success bit, an `(n+1)`-bit first time, and an `(n+1)`-bit return period. -/
abbrev visitScheduleWidth (n : ℕ) := (1 + (n + 1)) + (n + 1)

def visitScheduleFirst (v : State (visitScheduleWidth n)) : BitVec (n + 1) :=
  word fun i => v (Fin.castAdd (n + 1) (Fin.natAdd 1 i))

def visitSchedulePeriod (v : State (visitScheduleWidth n)) : BitVec (n + 1) :=
  word fun i => v (Fin.natAdd (1 + (n + 1)) i)

def visitScheduleContains (v : State (visitScheduleWidth n)) (t : ℕ) : Prop :=
  v (Fin.castAdd (n + 1) (0 : Fin (1 + (n + 1)))) = true ∧
    ∃ k, t = (visitScheduleFirst v).toNat + k * (visitSchedulePeriod v).toNat

/-- An arithmetic interpretation of a schedule; no additional-input gate bound is asserted. -/
def visitScheduleCount (v : State (visitScheduleWidth n)) (T : ℕ) : ℕ :=
  if v (Fin.castAdd (n + 1) (0 : Fin (1 + (n + 1)))) then
    arithmeticProgressionCount (visitScheduleFirst v).toNat (visitSchedulePeriod v).toNat T
  else 0

theorem visitScheduleCount_spec (v : State (visitScheduleWidth n)) (T : ℕ) :
    Set.ncard {t : ℕ | t ≤ T ∧ visitScheduleContains v t} = visitScheduleCount v T := by
  unfold visitScheduleCount visitScheduleContains
  split_ifs with hflag
  · simp only [hflag, true_and]
    exact arithmeticProgressionCount_spec _ _ _
  · have he : {t : ℕ | t ≤ T ∧
          v (Fin.castAdd (n + 1) (0 : Fin (1 + (n + 1)))) = true ∧
          ∃ k, t = (visitScheduleFirst v).toNat + k * (visitSchedulePeriod v).toNat} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, hflag, Bool.false_eq_true, false_and, and_false,
        Set.mem_empty_iff_false]
    rw [he, Set.ncard_empty]

/-- The returned record describes every visit time, with period zero encoding a singleton. -/
theorem visit_schedule_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + n) (visitScheduleWidth n),
      (∀ z t, (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z ↔
        visitScheduleContains (out.eval Boolean.interpretation z) t) ∧
      out.size ≤ 120000000 * (n + 1) * powerBudget n c.size (2 ^ n) L := by
  let f := c.eval Boolean.interpretation
  obtain ⟨nav, hn, hns⟩ := navigation_circuit c L hL hLN
  obtain ⟨period, hp, hps⟩ := minimal_period_circuit c L hL hLN
  have hnav := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (n + n)) nav id
    (fun bit => ⟨bit, rfl⟩)
  have hperiod := Synthesis.circuit (I := Boolean.interpretation) (s := inputs (n + n))
    period inputRight (fun bit => ⟨_, rfl⟩)
  let output := fun z => Fin.append (nav.eval Boolean.interpretation z)
    (period.eval Boolean.interpretation (inputRight z))
  have hs := (hnav.union hperiod).mono Set.Subset.rfl
    (show wires output ⊆ wires (nav.eval Boolean.interpretation) ∪
      wires (fun z => period.eval Boolean.interpretation (inputRight z)) from by
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp only [output, Fin.append_left]⟩
      | right i => exact Or.inr ⟨i, by simp only [output, Fin.append_right]⟩) le_rfl
  obtain ⟨out, ho, hsize⟩ := hs.exists_circuit_outputs
  refine ⟨out, fun z t => ?_, hsize.trans ?_⟩
  · rw [ho z]
    simp only [visitScheduleContains, visitScheduleFirst, visitSchedulePeriod, output,
      Fin.append_left, Fin.append_right, hp, hn z]
    have hflag := navigationBits_flag f (inputLeft z) (inputRight z)
    constructor
    · intro ht
      have hr : ∃ t, f^[t] (inputLeft z) = inputRight z := ⟨t, ht⟩
      have hd := navigationBits_time f (inputLeft z) (inputRight z) hr
      exact ⟨hflag.mpr hr, (visit_schedule_of_first f _ _ _ hd.1 hd.2.1 t).mp ht⟩
    · rintro ⟨hr, ht⟩
      have hd := navigationBits_time f (inputLeft z) (inputRight z) (hflag.mp hr)
      exact (visit_schedule_of_first f _ _ _ hd.1 hd.2.1 t).mpr ht
  · have hnB := hns.trans (navigationBudget_le n c.size L)
    have hcoef : 100000000 * (n + 1) + 11000000 ≤ 120000000 * (n + 1) := by
      nlinarith
    calc
      nav.size + period.size ≤ 100000000 * (n + 1) * powerBudget n c.size (2 ^ n) L +
          11000000 * powerBudget n c.size (2 ^ n) L := Nat.add_le_add hnB hps
      _ = (100000000 * (n + 1) + 11000000) * powerBudget n c.size (2 ^ n) L :=
        (Nat.add_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hcoef

theorem visit_schedule_optimized (c : Circuit Boolean.signature n n) :
    ∃ out : Circuit Boolean.signature (n + n) (visitScheduleWidth n),
      (∀ z t, (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z ↔
        visitScheduleContains (out.eval Boolean.interpretation z) t) ∧
      (∀ z T, Set.ncard {t : ℕ | t ≤ T ∧
        (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z} =
          visitScheduleCount (out.eval Boolean.interpretation z) T) ∧
      (out.size : ℝ) ≤ 360000000 * (n + 1) * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := visit_schedule_circuit c L hL hLN
  refine ⟨out, ho, fun z T => ?_, ?_⟩
  · rw [← visitScheduleCount_spec]
    congr 1
    ext t
    exact and_congr_right (fun _ => ho z t)
  · have hs' : (out.size : ℝ) ≤
      120000000 * (n + 1) * (powerBudget n c.size (2 ^ n) L : ℝ) := by exact_mod_cast hs
    have h := mul_le_mul_of_nonneg_left hopt (show 0 ≤ 120000000 * (n + 1 : ℝ) by positivity)
    nlinarith

end IteratedFunctions
