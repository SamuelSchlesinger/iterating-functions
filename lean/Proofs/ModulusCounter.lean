/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Words
public import Proofs.LinearArithmetic
public import Proofs.RecordCircuits
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Data.Nat.ModEq

/-! # The explicit permutation: one modular counter for each positive modulus -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

namespace ModulusCounter

/-- Inactive pairs are fixed, including modulus zero. -/
def advance (a b T : ℕ) : ℕ := if 0 < a ∧ b < a then (b + T) % a else b

@[simp] theorem advance_zero (a b : ℕ) : advance a b 0 = b := by
  by_cases h : 0 < a ∧ b < a
  · simp [advance, h, Nat.mod_eq_of_lt h.2]
  · simp [advance, h]

theorem advance_lt {a b U T : ℕ} (ha : a < U) (hb : b < U) : advance a b T < U := by
  unfold advance
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans ha
  · exact hb

theorem advance_add (a b S T : ℕ) :
    advance a (advance a b S) T = advance a b (S + T) := by
  by_cases h : 0 < a ∧ b < a
  · simp only [advance, h, and_self, ite_true, Nat.mod_lt _ h.1]
    rw [Nat.mod_add_mod, Nat.add_assoc]
  · simp [advance, h]

variable {k : ℕ}

def leftWord (x : State (k + k)) : BitVec k := word fun i => x (Fin.castAdd k i)
def rightWord (x : State (k + k)) : BitVec k := word fun i => x (Fin.natAdd k i)

def pack (a b : BitVec k) : State (k + k) :=
  Fin.append (fun i : Fin k => a.getLsbD i.val) (fun i : Fin k => b.getLsbD i.val)

@[simp] theorem leftWord_pack (a b : BitVec k) : leftWord (pack a b) = a := by
  simp only [leftWord, pack, Fin.append_left, word_bits]
@[simp] theorem rightWord_pack (a b : BitVec k) : rightWord (pack a b) = b := by
  simp only [rightWord, pack, Fin.append_right, word_bits]
@[simp] theorem pack_words (x : State (k + k)) : pack (leftWord x) (rightWord x) = x := by
  funext bit
  induction bit using Fin.addCases <;> simp [pack, leftWord, rightWord]

def power (T : ℕ) (x : State (k + k)) : State (k + k) :=
  pack (leftWord x) (BitVec.ofNat k (advance (leftWord x).toNat (rightWord x).toNat T))

@[simp] theorem power_zero (x : State (k + k)) : power 0 x = x := by
  simp [power]

theorem power_add (S T : ℕ) (x : State (k + k)) :
    power T (power S x) = power (S + T) x := by
  simp only [power, leftWord_pack, rightWord_pack, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (advance_lt (BitVec.isLt _) (BitVec.isLt _)), advance_add]

theorem iterate_power (T : ℕ) : (power (k := k) 1)^[T] = power T := by
  funext x
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih, power_add]

/-- The order common to every active modular counter. -/
def period (k : ℕ) : ℕ := Nat.lcmUpto (2 ^ k - 1)

theorem modulus_dvd_period {a : ℕ} (ha : 0 < a) (haU : a < 2 ^ k) : a ∣ period k := by
  change a ∣ (Finset.Icc 1 (2 ^ k - 1)).lcm id
  apply Finset.dvd_lcm
  simpa only [Finset.mem_Icc] using (show 1 ≤ a ∧ a ≤ 2 ^ k - 1 by lia)

theorem power_period (x : State (k + k)) : power (period k) x = x := by
  unfold power advance
  split_ifs with h
  · have hd := modulus_dvd_period h.1 (BitVec.isLt (leftWord x))
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt h.2]
    simp
  · simp

theorem power_bijective : Function.Bijective (power (k := k) 1) := by
  have hpos : 0 < period k := Nat.lcmUpto_pos _
  constructor
  · intro x y he
    have h := congrArg (power (period k - 1)) he
    simpa only [power_add, show 1 + (period k - 1) = period k by lia, power_period] using h
  · intro y
    exact ⟨power (period k - 1) y, by
      rw [power_add, Nat.sub_add_cancel hpos, power_period]⟩

/-- Different residues modulo the common period give different Boolean functions. -/
theorem powers_injective : Function.Injective (fun T : Fin (period k) => power (k := k) T.val) := by
  intro S T he
  have hmod (a : ℕ) (ha : 0 < a) (haU : a < 2 ^ k) : S.val % a = T.val % a := by
    have hx := congrArg (fun f => (rightWord (f
      (pack (BitVec.ofNat k a) (BitVec.ofNat k 0)))).toNat) he
    have hslt := (Nat.mod_lt S.val ha).trans haU
    have htlt := (Nat.mod_lt T.val ha).trans haU
    simpa [power, advance, Nat.mod_eq_of_lt haU, ha, Nat.mod_eq_of_lt hslt,
      Nat.mod_eq_of_lt htlt] using hx
  have helper (S T : ℕ) (hST : S ≤ T)
      (hmod : ∀ a, 0 < a → a < 2 ^ k → S % a = T % a) : period k ∣ T - S := by
    change (Finset.Icc 1 (2 ^ k - 1)).lcm id ∣ T - S
    apply Finset.lcm_dvd
    intro a ha
    have ha' : 1 ≤ a ∧ a ≤ 2 ^ k - 1 := Finset.mem_Icc.mp ha
    have hm : Nat.ModEq a S T := hmod a (by lia) (by have := Nat.one_le_two_pow (n := k); lia)
    exact (Nat.modEq_iff_dvd' hST).mp hm
  apply Fin.ext
  rcases le_total S.val T.val with h | h
  · have hd := helper S.val T.val h hmod
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by have := T.isLt; lia)
    lia
  · have hd := helper T.val S.val h (fun a ha hU => (hmod a ha hU).symm)
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by have := S.isLt; lia)
    lia

end ModulusCounter
end IteratedFunctions
