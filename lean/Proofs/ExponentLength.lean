/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CounterRemainders
public import Proofs.LowerBound
import Mathlib.Tactic.Linarith

/-! # Hard powers of the modulus-counter permutation need long exponents -/

@[expose] public section

namespace IteratedFunctions.ModulusCounter

open Cslib.Circuits

/-- Hardwiring `m` numerator bits and masking the zero modulus charges all constants. -/
theorem short_remainder_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit Boolean.signature k k,
      out.Computes Boolean.interpretation (remainder T) ∧
      out.size ≤ m * (51 * (k + 1) + 4) + 10 * (k + 1) := by
  obtain ⟨rem, hrem, hsize⟩ := bounded_modulus_remainder m k
  let constants : Set (State k → Bool) := {fun _ => false, fun _ => true}
  let s := inputs k ∪ constants
  have hc (b : Bool) : (fun _ : State k => b) ∈ s := by cases b <;> simp [s, constants]
  let bits := fun i : Fin m => (BitVec.ofNat m T).getLsbD i.val
  let init := fun x : State k => Fin.append bits x
  let r := fun x => word (rem.eval Boolean.interpretation (init x))
  have hi (i : Fin (m + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => simpa only [init, Fin.append_left] using hc (bits i)
    | right i => simpa only [init, Fin.append_right] using
        (show (fun x : State k => x i) ∈ s from Or.inl ⟨i, rfl⟩)
  have hr := Synthesis.circuit (I := Boolean.interpretation) (s := s) rem init hi
  have hz := synthesis_word_eq_const s (fun x : State k => word x)
    (fun i => by simpa only [word_bit] using
      (show (fun x : State k => x i) ∈ s from Or.inl ⟨i, rfl⟩)) 0
  let s1 := s ∪ (wires (fun x => rem.eval Boolean.interpretation (init x)) ∪
    {fun x => decide (word x = (0 : BitVec k))})
  have hm := synthesis_word_mux s1 (fun _ => (0 : BitVec k)) r
    (fun x => decide (word x = (0 : BitVec k))) (Or.inr (Or.inr rfl))
    (fun i => Or.inl (hc _)) (fun i => by
      simpa only [r, word_bit] using
        (show (fun x => rem.eval Boolean.interpretation (init x) i) ∈ s1 from
          Or.inr (Or.inl ⟨i, rfl⟩)))
  have hconst : Synthesis Boolean.interpretation (inputs k) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have h := hconst.trans ((hr.union hz).trans hm)
  have hval (x : State k) :
      (if decide (word x = (0 : BitVec k)) then (0 : BitVec k) else r x) =
        word (remainder T x) := by
    rw [remainder_word]
    have hzero : word x = (0 : BitVec k) ↔ (word x).toNat = 0 := by
      rw [← BitVec.toNat_inj]
      simp
    simp only [decide_eq_true_eq, hzero]
    split_ifs with hz
    · simp
    · have hp : 0 < (word x).toNat := Nat.pos_of_ne_zero hz
      have hspec := hrem (init x)
      simp only [init, Fin.append_right, Fin.append_left, bits, binaryValue_bits,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT] at hspec
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.mod_lt _ hp).trans (word x).isLt)]
      exact hspec hp
  have hout : wires (remainder (k := k) T) ⊆
      wordWires (fun x => if decide (word x = (0 : BitVec k)) then 0 else r x) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    funext x
    simp only [hval, word_bit]
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by lia⟩

/-- A fixed exponent fitting in `m` bits gives a circuit linear in `m(k+1)`. -/
theorem short_power_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit Boolean.signature (k + k) (k + k),
      out.Computes Boolean.interpretation (power T) ∧
      out.size ≤ 110 * (m + 1) * (k + 1) := by
  obtain ⟨rem, hr, hs⟩ := short_remainder_circuit k m T hT
  obtain ⟨out, ho, hb⟩ := power_of_remainder T rem hr
  refine ⟨out, ho, ?_⟩
  have hm : 4 * m ≤ 4 * m * (k + 1) := Nat.le_mul_of_pos_right _ (by lia)
  nlinarith

/-- Any exponent yielding the established lower bound needs this much binary capacity.
The statement uses `T < 2^m`, so it applies to every encoding width, including
the minimal binary length, without choosing a convention for the length of zero. -/
theorem hard_power_requires_long_exponent (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit Boolean.signature (k + k) (k + k),
      c.Computes Boolean.interpretation (power T) → lowerBudget k < c.size) :
    lowerBudget k < 110 * (m + 1) * (k + 1) := by
  obtain ⟨out, ho, hs⟩ := short_power_circuit k m T hT
  exact (hard out ho).trans_le hs

/-- An explicit form of the exponential lower bound on exponent length. -/
theorem hard_power_exponent_capacity (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit Boolean.signature (k + k) (k + k),
      c.Computes Boolean.interpretation (power T) → lowerBudget k < c.size) :
    2 ^ k < 112640 * (m + 1) * (k + 1) ^ 2 := by
  have h := hard_power_requires_long_exponent k m T hT hard
  change 2 ^ k / (1024 * (k + 1)) < _ at h
  have hn := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 1024 * (k + 1))).mp h
  nlinarith

end IteratedFunctions.ModulusCounter
