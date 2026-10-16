/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ActiveCheckpoints
public import Proofs.FixedPower
import Mathlib.Tactic.Linarith

/-! # Fixed-power circuits parameterized by long-trajectory mass -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Algebraic.MassProduction.Sorting

theorem active_construction_cost (n s M L d : ℕ) (hL : 0 < L) (hd : d ≤ n + 3)
    (hR : 2 ^ d ≤ 2 * (M + 4 * L + 1)) :
    2 + 5 * (4 * L) * s + (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 3) + 1) +
      1000 * (4 * L + 1) * (n + (n + 3) + 1) ^ 2 ≤
      120000 * (L * s + (n + 1) ^ 3 * (L + M + 1)) := by
  have h1 : 18 * d ^ 2 + 30 ≤ 192 * (n + 1) ^ 2 := by
    have hs : d ^ 2 ≤ (n + 3) ^ 2 := by gcongr
    nlinarith
  have h2 : Record.width n (n + 3) + 1 ≤ 6 * (n + 1) := by unfold Record.width; lia
  have hs : (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 3) + 1) ≤
      (192 * (n + 1) ^ 2) * (2 * (M + 4 * L + 1)) * (6 * (n + 1)) := by gcongr
  have h3 : (n + (n + 3) + 1) ^ 2 ≤ 16 * (n + 1) ^ 2 := by nlinarith
  have hh : 1000 * (4 * L + 1) * (n + (n + 3) + 1) ^ 2 ≤
      1000 * (5 * L) * (16 * (n + 1) ^ 2) := by gcongr; lia
  nlinarith [Nat.zero_le (L * n ^ 3), Nat.zero_le (M * n ^ 3),
    Nat.zero_le (M * n ^ 2), Nat.zero_le (L * n ^ 2), Nat.zero_le (L * s)]

/-- Replace ambient state count by the number of deep states and long-cycle vertices.
The parameter depends on `L`, so no optimization treating it as constant is implicit. -/
theorem active_mass_fixed_power (n : ℕ) (c : Circuit Boolean.signature n n) (T L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation (c.eval Boolean.interpretation)^[T] ∧
      out.size ≤ 120000 * powerBudget n c.size
        (activeVertices (c.eval Boolean.interpretation) L).card L := by
  classical
  let f := c.eval Boolean.interpretation
  by_cases hT : T < 4 * L
  · refine ⟨c.iterate T, (unroll_spec c Boolean.interpretation T).1, ?_⟩
    rw [(unroll_spec c Boolean.interpretation T).2]
    have ht : T * c.size ≤ 4 * L * c.size := Nat.mul_le_mul_right _ hT.le
    unfold powerBudget
    nlinarith [Nat.zero_le ((n + 1) ^ 3 * (L + (activeVertices f L).card / L + 1))]
  obtain ⟨H, _, hcard, hcover⟩ := exists_active_checkpoints f L hL
  let cp : Fin H.card → State n := fun j => (H.equivFin.symm j).val
  let d := Nat.clog 2 (H.card + 4 * L + 1)
  have hcapacity : H.card + (4 * L + 1) ≤ networkRecords d := by
    simpa only [networkRecords_eq_two_pow, d, Nat.add_assoc] using
      Nat.le_pow_clog (by decide : 1 < 2) (H.card + 4 * L + 1)
  have hN : H.card ≤ 2 ^ n := by
    have h := Finset.card_le_univ H
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using h
  have hd : d ≤ n + 3 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    lia
  have hR : 2 ^ d ≤ 2 * (H.card + 4 * L + 1) := by
    have hpos : 0 < d := Nat.clog_pos (by decide) (by lia)
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
      (show 1 < H.card + 4 * L + 1 by lia)
    have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← Nat.pow_succ, show (d - 1).succ = d by lia]
    rw [hpow]
    change 2 ^ (d - 1) < _ at hp
    lia
  have hfit : 4 * L < 2 ^ (n + 3) := by
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    lia
  obtain ⟨out, hout, hsize⟩ := exists_fixedOutput (w := n + 3) c T (4 * L) d cp
  refine ⟨out, ?_, ?_⟩
  · intro x
    rw [hout x]
    apply reconstruct_spec f T (4 * L) cp x _ _ hfit (by lia)
    apply Record.detect_sorted_witness f T (4 * L) d cp x hcapacity hfit
    rcases hcover x with ⟨i, j, hij, hj, heq⟩ | ⟨t, ht, hmem⟩
    · exact Or.inr ⟨i, j, hij, by lia, heq⟩
    · refine Or.inl ⟨t, ht.le, H.equivFin ⟨f^[t] x, hmem⟩, ?_⟩
      simp [cp]
  · have hc : H.card ≤ (activeVertices f L).card / L :=
      (Nat.le_div_iff_mul_le hL).mpr hcard
    apply hsize.trans ((active_construction_cost n c.size H.card L d hL hd hR).trans ?_)
    unfold powerBudget
    gcongr

end IteratedFunctions
