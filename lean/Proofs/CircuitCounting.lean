/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Optimization
public import Complexitylib.Algebraic.LowerBound.Counting.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Explicit description counts for the native Boolean circuit model -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

theorem boolean_lineCount_le (w : ℕ) :
    Boolean.signature.lineCount w ≤ 5 * (w + 1) ^ 2 := by
  unfold Signature.lineCount
  have h (op : Boolean.Op) : w ^ Boolean.signature.Arity op ≤ (w + 1) ^ 2 := by
    calc
      _ ≤ (w + 1) ^ Boolean.signature.Arity op := Nat.pow_le_pow_left (by lia) _
      _ ≤ (w + 1) ^ 2 := Nat.pow_le_pow_right (by lia)
        (by cases op <;> simp)
  calc
    _ ≤ ∑ _ : Boolean.Op, (w + 1) ^ 2 := Finset.sum_le_sum fun op _ => h op
    _ = _ := by simp

/-- Constants, arbitrary fanout, and all designated outputs are counted. -/
theorem boolean_orderedBudget_le (n m q : ℕ) :
    Boolean.signature.orderedBudget n m q ≤
      (q + 1) * 5 ^ q * (n + q + 1) ^ (2 * q + m) := by
  let W := n + q + 1
  have hW : 1 ≤ W := by dsimp [W]; lia
  have ht (g : ℕ) (hg : g ∈ Finset.range (q + 1)) :
      (∏ j ∈ Finset.range g, Boolean.signature.lineCount (n + j)) * (n + g) ^ m ≤
        5 ^ q * W ^ (2 * q + m) := by
    have hgq : g ≤ q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hg
    have hp : (∏ j ∈ Finset.range g, Boolean.signature.lineCount (n + j)) ≤
        (5 * W ^ 2) ^ g := by
      calc
        _ ≤ ∏ _j ∈ Finset.range g, 5 * W ^ 2 := by
          apply Finset.prod_le_prod
          intro j hj
          have hjq : n + j + 1 ≤ W := by have := Finset.mem_range.mp hj; dsimp [W]; lia
          exact (boolean_lineCount_le _).trans (by gcongr)
        _ = _ := by simp
    calc
      _ ≤ (5 * W ^ 2) ^ g * W ^ m := by gcongr; dsimp [W]; lia
      _ ≤ (5 * W ^ 2) ^ q * W ^ m := by
        gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
  unfold Signature.orderedBudget
  calc
    _ ≤ ∑ _g ∈ Finset.range (q + 1), 5 ^ q * W ^ (2 * q + m) := Finset.sum_le_sum ht
    _ = _ := by simp [W]; ring

/-- A convenient binary logarithmic bound when the wire budget is at most `2^h`. -/
theorem boolean_orderedBudget_le_pow (n m q h : ℕ) (hw : n + q + 1 ≤ 2 ^ h) :
    Boolean.signature.orderedBudget n m q ≤ 2 ^ (3 * q + h * (2 * q + m + 1)) := by
  calc
    _ ≤ (q + 1) * 5 ^ q * (n + q + 1) ^ (2 * q + m) := boolean_orderedBudget_le _ _ _
    _ ≤ 2 ^ h * (2 ^ 3) ^ q * (2 ^ h) ^ (2 * q + m) := by
      gcongr
      · lia
      · decide
    _ = _ := by simp only [← pow_mul, ← pow_add]; congr 1; ring

/-- The deliberately generous threshold makes the polynomial comparison elementary. -/
theorem square_le_exponential (k : ℕ) (hk : 64 ≤ k) :
    128 * (k + 2) ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 by rw [Nat.pow_succ]]
    have hsq : (k + 1 + 2) ^ 2 ≤ 2 * (k + 2) ^ 2 := by nlinarith
    nlinarith

def lowerBudget (k : ℕ) : ℕ := 2 ^ k / (1024 * (k + 1))

/-- The number of descriptions below the target lower bound is far below the LCM scale. -/
theorem lowerBudget_description_exponent (k : ℕ) (hk : 64 ≤ k) :
    let q := lowerBudget k
    3 * q + (k + 2) * (2 * q + (k + k) + 1) + k < 2 ^ k - 1 := by
  dsimp only
  have hq : lowerBudget k * (1024 * (k + 1)) ≤ 2 ^ k := Nat.div_mul_le_self _ _
  have hs := square_le_exponential k hk
  have hpoly : (k + 2) * (k + k + 1) + k + 2 ≤ 4 * (k + 2) ^ 2 := by nlinarith
  have hcoef : (2 * (k + 2) + 3) * 128 ≤ 1024 * (k + 1) := by lia
  have hq' := Nat.mul_le_mul_right (lowerBudget k) hcoef
  have htotal : 128 * (3 * lowerBudget k +
      (k + 2) * (2 * lowerBudget k + (k + k) + 1) + k + 2) ≤ 5 * 2 ^ k := by
    nlinarith
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  lia

theorem lowerBudget_wire_bound (k : ℕ) (hk : 64 ≤ k) :
    k + k + lowerBudget k + 1 ≤ 2 ^ (k + 2) := by
  have hq : lowerBudget k ≤ 2 ^ k := Nat.div_le_self _ _
  have hs := square_le_exponential k hk
  simp only [Nat.pow_succ]
  nlinarith

end IteratedFunctions
