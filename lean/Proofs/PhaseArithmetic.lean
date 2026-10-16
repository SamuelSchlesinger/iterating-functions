/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Division
public import Proofs.HittingTimes
import Mathlib.Tactic.Linarith

/-! # Bounded-word modular phase corrections -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n w : ℕ}

def subtractModNat (a b m : ℕ) : ℕ := (a + m - b % m) % m

theorem subtractModNat_cancel (a b m : ℕ) (hm : 0 < m) :
    Nat.ModEq m (subtractModNat a b m + b) a := by
  unfold Nat.ModEq subtractModNat
  calc
    _ = (a + m - b % m + b % m) % m := by simp only [Nat.add_mod, Nat.mod_mod]
    _ = a % m := by
      rw [Nat.sub_add_cancel (show b % m ≤ a + m from (Nat.mod_lt _ hm).le.trans (by lia)),
        Nat.add_mod_right]

theorem subtractModNat_eq {a b m c : ℕ} (hm : 0 < m) (hc : c < m)
    (he : Nat.ModEq m (c + b) a) : subtractModNat a b m = c := by
  have hh := Nat.ModEq.add_right_cancel' b ((subtractModNat_cancel a b m hm).trans he.symm)
  simpa only [Nat.ModEq, subtractModNat, Nat.mod_mod, Nat.mod_eq_of_lt hc] using hh

def subtractMod (a b m : BitVec w) : BitVec w := (a + m - b % m) % m

theorem subtractMod_spec (a b m : BitVec w) (hm : 0 < m.toNat)
    (hfit : a.toNat + m.toNat < 2 ^ w) :
    (subtractMod a b m).toNat = subtractModNat a.toNat b.toNat m.toNat := by
  have hrem : (b % m).toNat ≤ (a + m).toNat := by
    simp only [BitVec.toNat_umod, BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
    exact (Nat.mod_lt _ hm).le.trans (by lia)
  simp only [subtractMod, BitVec.toNat_umod, BitVec.toNat_sub_of_le hrem,
    BitVec.toNat_add, Nat.mod_eq_of_lt hfit, subtractModNat]

/-- Two remainders, one addition, and one subtraction; all are Boolean circuits. -/
theorem synthesis_subtractMod (s : Set (State n → Bool)) (a b m : State n → BitVec w)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s)
    (hm : ∀ i : Fin w, (fun x => (m x).getLsbD i.val) ∈ s) :
    Synthesis Boolean.interpretation s (wordWires fun x => subtractMod (a x) (b x) (m x))
      (300 * (w + 1) ^ 3) := by
  have hadd := synthesis_add s a m ha hm
  have hrem := synthesis_umod s b m hb hm
  let src := s ∪ (wordWires (fun x => a x + m x) ∪ wordWires (fun x => b x % m x))
  have hsub := synthesis_sub src (fun x => a x + m x) (fun x => b x % m x)
    (fun i => Or.inr (Or.inl ⟨i, rfl⟩)) (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
  have hfinal := synthesis_umod (src ∪ wordWires (fun x => a x + m x - b x % m x))
    (fun x => a x + m x - b x % m x) m (fun i => Or.inr ⟨i, rfl⟩)
    (fun i => Or.inl (Or.inl (hm i)))
  exact ((hadd.union hrem).trans (hsub.trans hfinal)).mono
    Set.Subset.rfl Set.Subset.rfl (by
      have h := Nat.pow_le_pow_right (show 1 ≤ w + 1 by lia) (show 2 ≤ 3 by decide)
      lia)

end IteratedFunctions
