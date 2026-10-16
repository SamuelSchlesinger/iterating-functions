/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.BinaryNumbers
public import Proofs.Arithmetic
import Mathlib.Tactic.Linarith

/-! # Finding a bounded threshold with one query per binary digit -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

def searchBelow (n μ : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if searchBelow n μ j + 2 ^ (n - j - 1) < μ
    then searchBelow n μ j + 2 ^ (n - j - 1) else searchBelow n μ j

theorem searchBelow_bounds (n μ : ℕ) (hμ : μ ≤ 2 ^ n) (j : ℕ) (hj : j ≤ n) :
    (μ = 0 → searchBelow n μ j = 0) ∧
      (0 < μ → searchBelow n μ j < μ ∧ μ ≤ searchBelow n μ j + 2 ^ (n - j)) := by
  induction j with
  | zero => simp [searchBelow, hμ]
  | succ j ih =>
    obtain ⟨hz, hlo⟩ := ih (by lia)
    have hp : 2 ^ (n - j) = 2 ^ (n - j - 1) * 2 := by
      calc
        _ = 2 ^ ((n - j - 1) + 1) := by congr 1; lia
        _ = _ := Nat.pow_succ _ _
    constructor
    · intro h
      rw [searchBelow]
      simp only [h, Nat.not_lt_zero, ite_false]
      simpa only [h] using hz h
    · intro h
      obtain ⟨ha, hb⟩ := hlo h
      rw [hp] at hb
      have he : n - (j + 1) = n - j - 1 := by lia
      rw [searchBelow, he]
      split_ifs <;> constructor <;> lia

theorem searchBelow_lt (n μ j : ℕ) (hμ : μ < 2 ^ n) (hj : j ≤ n) :
    searchBelow n μ j < 2 ^ n := by
  obtain ⟨hz, hp⟩ := searchBelow_bounds n μ hμ.le j hj
  rcases Nat.eq_zero_or_pos μ with h | h
  · rw [hz h]
    positivity
  · exact (hp h).1.trans hμ

theorem searchBelow_result (n μ : ℕ) (hμ : μ ≤ 2 ^ n) :
    (if μ = 0 then 0 else searchBelow n μ n + 1) = μ := by
  obtain ⟨_, hp⟩ := searchBelow_bounds n μ hμ n le_rfl
  split_ifs with h
  · exact h.symm
  · obtain ⟨ha, hb⟩ := hp (by lia)
    simp only [Nat.sub_self, pow_zero] at hb
    lia

/-- The source contains both constants. The query is a charged Boolean construction for `μ ≤ j`. -/
theorem synthesis_threshold {a : ℕ} (s : Set (State a → Bool)) (μ : State a → ℕ) (n C : ℕ)
    (hμ : ∀ x, μ x < 2 ^ n) (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s)
    (query : ∀ (src : Set (State a → Bool)), s ⊆ src →
      ∀ value : State a → BitVec (n + 2), wordWires value ⊆ src →
        Synthesis Boolean.interpretation src {fun x => decide (μ x ≤ (value x).toNat)} C) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => BitVec.ofNat (n + 2) (μ x))
      ((n + 1) * (C + 100 * (n + 3) ^ 2)) := by
  let value := fun j x => BitVec.ofNat (n + 2) (searchBelow n (μ x) j)
  let q := fun j => wordWires (value j)
  have hv (j : ℕ) (hj : j ≤ n) (x : State a) :
      (value j x).toNat = searchBelow n (μ x) j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact (searchBelow_lt n (μ x) j (hμ x) hj).trans_le (by gcongr; lia)
  have hz : q 0 ⊆ s := by
    rintro _ ⟨bit, rfl⟩
    simpa [value, searchBelow] using hc false
  have hstep (j : ℕ) (hj : j < n) :
      Synthesis Boolean.interpretation (s ∪ Synthesis.stages q j) (q (j + 1))
        (C + 100 * (n + 3) ^ 2) := by
    let src := s ∪ Synthesis.stages q j
    have hav (i : Fin (n + 2)) : (fun x => (value j x).getLsbD i.val) ∈ src :=
      Or.inr (Synthesis.mem_stages q j ⟨i, rfl⟩)
    let candidate := fun x => value j x + BitVec.ofNat (n + 2) (2 ^ (n - j - 1))
    have hcand (x : State a) : (candidate x).toNat = searchBelow n (μ x) j + 2 ^ (n - j - 1) := by
      have hs := searchBelow_lt n (μ x) j (hμ x) (by lia)
      have hp : 2 ^ (n - j - 1) ≤ 2 ^ n := by gcongr; lia
      have hn : 0 < 2 ^ n := by positivity
      have hfit : searchBelow n (μ x) j + 2 ^ (n - j - 1) < 2 ^ (n + 2) := by
        simp only [Nat.pow_succ]
        lia
      have hpow : 2 ^ (n - j - 1) < 2 ^ (n + 2) := by
        simp only [Nat.pow_succ]
        lia
      simp only [candidate, BitVec.toNat_add, hv j (by lia), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hpow, Nat.mod_eq_of_lt hfit]
    have hadd := synthesis_add src (value j) (fun _ => BitVec.ofNat (n + 2) (2 ^ (n - j - 1)))
      hav (fun i => Or.inl (hc _))
    let src1 := src ∪ wordWires candidate
    have htest := query src1 (fun _ h => Or.inl (Or.inl h)) candidate (fun _ h => Or.inr h)
    have hm := synthesis_word_mux (src1 ∪ {fun x => decide (μ x ≤ (candidate x).toNat)})
      (value j) candidate (fun x => decide (μ x ≤ (candidate x).toNat)) (Or.inr rfl)
      (fun i => Or.inl (Or.inl (hav i))) (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
    have he (x : State a) :
        (if decide (μ x ≤ (candidate x).toNat) then value j x else candidate x) =
        value (j + 1) x := by
      apply BitVec.eq_of_toNat_eq
      simp only [decide_eq_true_eq, hcand]
      by_cases hh : searchBelow n (μ x) j + 2 ^ (n - j - 1) < μ x
      · rw [ite_eq_right (by lia)]
        rw [hcand, hv (j + 1) (by lia), searchBelow, ite_eq_left hh]
      · rw [ite_eq_left (by lia)]
        rw [hv j (by lia), hv (j + 1) (by lia), searchBelow, ite_eq_right hh]
    have h := hadd.trans (htest.trans hm)
    simp only [he] at h
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)
  have hsteps := Synthesis.steps q (C + 100 * (n + 3) ^ 2) n hz hstep
  let src := s ∪ Synthesis.stages q n
  have hav (i : Fin (n + 2)) : (fun x => (value n x).getLsbD i.val) ∈ src :=
    Or.inr (Synthesis.mem_stages q n ⟨i, rfl⟩)
  let plus := fun x => value n x + 1
  have hadd := synthesis_add src (value n) (fun _ => (1 : BitVec (n + 2))) hav
    (fun i => Or.inl (hc _))
  let src1 := src ∪ wordWires plus
  have htest := query src1 (fun _ h => Or.inl (Or.inl h)) (fun _ => 0)
    (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (hc _)))
  have hm := synthesis_word_mux (src1 ∪ {fun x => decide (μ x ≤ (0 : BitVec (n + 2)).toNat)})
    (fun _ => 0) plus (fun x => decide (μ x ≤ (0 : BitVec (n + 2)).toNat)) (Or.inr rfl)
    (fun i => Or.inl (Or.inl (Or.inl (hc _)))) (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
  have he (x : State a) :
      (if decide (μ x ≤ (0 : BitVec (n + 2)).toNat) then 0 else plus x) =
        BitVec.ofNat (n + 2) (μ x) := by
    have hn : 1 < 2 ^ (n + 2) := by
      simp only [Nat.pow_succ]
      have := Nat.one_le_two_pow (n := n)
      lia
    have hs := searchBelow_result n (μ x) (hμ x).le
    by_cases hz : μ x = 0
    · simp [hz]
    · simp only [hz, ite_false] at hs
      apply BitVec.eq_of_toNat_eq
      simp only [show (0 : BitVec (n + 2)).toNat = 0 by simp,
        show ¬ μ x ≤ 0 by lia, decide_false, Bool.false_eq_true, ite_false, plus,
        BitVec.toNat_add, hv n le_rfl, BitVec.toNat_ofNat,
        show (1 : BitVec (n + 2)).toNat = 1 by simp [Nat.mod_eq_of_lt hn], hs]
  have h := hsteps.trans (hadd.trans (htest.trans hm))
  simp only [he] at h
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

end IteratedFunctions
