/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.VariableTime
public import Proofs.Words

/-! # Agreement between input exponent bits and bounded words -/

@[expose] public section

namespace IteratedFunctions

variable {w : ℕ}

theorem binaryValue_bits (a : BitVec w) :
    binaryValue (fun i : Fin w => a.getLsbD i.val) = a.toNat := by
  have h (j : ℕ) (hj : j ≤ w) :
      partialValue (fun i : Fin w => a.getLsbD i.val) j = a.toNat % 2 ^ j := by
    induction j with
    | zero => simp only [partialValue_zero, pow_zero, Nat.mod_one]
    | succ j ih =>
      rw [partialValue_succ _ (by lia), ih (by lia)]
      have hd := Nat.mod_add_div (a.toNat % (2 ^ j * 2)) (2 ^ j)
      rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self] at hd
      have hq : a.toNat / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by decide)
      have ht : a.getLsbD j = decide (a.toNat / 2 ^ j % 2 = 1) :=
        Nat.testBit_eq_decide_div_mod_eq
      rw [ht, Nat.pow_succ]
      by_cases he : a.toNat / 2 ^ j % 2 = 1
      · simp only [he, decide_true, ite_true, Nat.mul_one] at hd ⊢
        exact hd
      · have hz : a.toNat / 2 ^ j % 2 = 0 := by lia
        simp only [hz, reduceCtorEq, decide_false, ite_false, Nat.mul_zero, Nat.add_zero] at hd ⊢
        exact hd
  simpa only [partialValue_all, Nat.mod_eq_of_lt a.isLt] using h w le_rfl

@[simp] theorem word_toNat (bits : Fin w → Bool) :
    (word bits).toNat = binaryValue bits := by
  simpa only [word_bit] using (binaryValue_bits (word bits)).symm

end IteratedFunctions
