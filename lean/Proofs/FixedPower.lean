/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Construction
public import Proofs.Checkpoints
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# The fixed-power bound

The construction works on a finite invariant subset of the bit-string state
space. The ambient-space theorem is the specialization to all bit strings.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits Algebraic.MassProduction.Sorting

theorem construction_cost (n s M L d : ℕ) (hL : 0 < L) (hd : d ≤ n + 2)
    (hR : 2 ^ d ≤ 2 * (M + 2 * L + 1)) :
    2 + 5 * (2 * L) * s + (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 2) + 1) +
      1000 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 ≤
      40000 * (L * s + (n + 1) ^ 3 * (L + M + 1)) := by
  have h1 : 18 * d ^ 2 + 30 ≤ 102 * (n + 1) ^ 2 := by
    have hs : d ^ 2 ≤ (n + 2) ^ 2 := by gcongr
    nlinarith
  have h2 : Record.width n (n + 2) + 1 ≤ 5 * (n + 1) := by unfold Record.width; lia
  have hs : (18 * d ^ 2 + 30) * 2 ^ d * (Record.width n (n + 2) + 1) ≤
      (102 * (n + 1) ^ 2) * (2 * (M + 2 * L + 1)) * (5 * (n + 1)) := by gcongr
  have h3 : (n + (n + 2) + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 := by nlinarith
  have hh : 1000 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 ≤
      1000 * (3 * L) * (9 * (n + 1) ^ 2) := by gcongr; lia
  nlinarith [Nat.zero_le (L * n ^ 3), Nat.zero_le (M * n ^ 3),
    Nat.zero_le (M * n ^ 2), Nat.zero_le (L * n ^ 2), Nat.zero_le (L * s)]

/-- A concrete, uniform constant for the invariant-set fixed-power tradeoff. -/
theorem fixed_power_on (n : ℕ) (c : Circuit Boolean.signature n n) (S : Finset (State n))
    (T L : ℕ) (hS : ∀ x ∈ S, c.eval Boolean.interpretation x ∈ S)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      out.ComputesOn Boolean.interpretation S (c.eval Boolean.interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget n c.size S.card L := by
  classical
  let f := c.eval Boolean.interpretation
  by_cases hT : T < 2 * L
  · refine ⟨c.iterate T, fun x _ => (unroll_spec c Boolean.interpretation T).1 x, ?_⟩
    rw [(unroll_spec c Boolean.interpretation T).2]
    have ht : T * c.size ≤ 2 * L * c.size := Nat.mul_le_mul_right _ hT.le
    unfold powerBudget
    nlinarith [Nat.zero_le ((n + 1) ^ 3 * (L + S.card / L + 1))]
  obtain ⟨H, hHS, hcard, hcover⟩ := exists_checkpoints f S hS hL
  let cp : Fin H.card → State n := fun j => (H.equivFin.symm j).val
  let d := Nat.clog 2 (H.card + 2 * L + 1)
  have hcapacity : H.card + (2 * L + 1) ≤ networkRecords d := by
    simpa only [networkRecords_eq_two_pow, d, Nat.add_assoc] using
      Nat.le_pow_clog (by decide : 1 < 2) (H.card + 2 * L + 1)
  have hN : H.card ≤ 2 ^ n := by
    have h := Finset.card_le_univ H
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using h
  have hd : d ≤ n + 2 := by
    apply Nat.clog_le_of_le_pow
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    lia
  have hR : 2 ^ d ≤ 2 * (H.card + 2 * L + 1) := by
    have hpos : 0 < d := Nat.clog_pos (by decide) (by lia)
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
      (show 1 < H.card + 2 * L + 1 by lia)
    have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← Nat.pow_succ, show (d - 1).succ = d by lia]
    rw [hpow]
    change 2 ^ (d - 1) < _ at hp
    lia
  have hfit : 2 * L < 2 ^ (n + 2) := by
    simp only [Nat.pow_succ]
    have := Nat.one_le_two_pow (n := n)
    lia
  obtain ⟨out, hout, hsize⟩ := exists_fixedOutput (w := n + 2) c T (2 * L) d cp
  refine ⟨out, ?_, ?_⟩
  · intro x hx
    rw [hout x]
    apply reconstruct_spec f T (2 * L) cp x _ _ hfit (by lia)
    apply Record.detect_sorted_witness f T (2 * L) d cp x hcapacity hfit
    rcases hcover x hx with ⟨i, j, hij, hj, heq⟩ | ⟨t, ht, hmem⟩
    · exact Or.inr ⟨i, j, hij, by lia, heq⟩
    · refine Or.inl ⟨t, ht.le, H.equivFin ⟨f^[t] x, hmem⟩, ?_⟩
      simp [cp]
  · have hc : H.card ≤ S.card / L := (Nat.le_div_iff_mul_le hL).mpr hcard
    apply hsize.trans ((construction_cost n c.size H.card L d hL hd hR).trans ?_)
    unfold powerBudget
    gcongr

theorem fixedPowerOnBound : FixedPowerOnBound := ⟨40000, fixed_power_on⟩

/-- The original fixed-power tradeoff, now for actual Boolean circuits. -/
theorem fixed_power (n : ℕ) (c : Circuit Boolean.signature n n) (T L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      out.Computes Boolean.interpretation (c.eval Boolean.interpretation)^[T] ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L := by
  classical
  obtain ⟨out, hout, hsize⟩ := fixed_power_on n c Finset.univ T L
    (fun _ _ => Finset.mem_univ _) hL hLN
  exact ⟨out, fun x => hout (Finset.mem_univ x), by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      using hsize⟩

theorem fixedPowerBound : FixedPowerBound := ⟨40000, fixed_power⟩

end IteratedFunctions
