/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Optimization

/-! # An iteration count supplied as input -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

variable {n m w : ℕ}

/-- Least-significant-bit-first binary value. -/
def binaryValue (bits : Fin m → Bool) : ℕ :=
  ∑ j : Fin m, if bits j then 2 ^ j.val else 0

def partialValue (bits : Fin m → Bool) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if hi : i < m then (if bits ⟨i, hi⟩ then 2 ^ i else 0) else 0

@[simp] theorem partialValue_zero (bits : Fin m → Bool) : partialValue bits 0 = 0 := by
  simp [partialValue]

theorem partialValue_succ (bits : Fin m → Bool) {j : ℕ} (hj : j < m) :
    partialValue bits (j + 1) = partialValue bits j + (if bits ⟨j, hj⟩ then 2 ^ j else 0) := by
  simp [partialValue, Finset.sum_range_succ, hj]

@[simp] theorem partialValue_all (bits : Fin m → Bool) :
    partialValue bits m = binaryValue bits := by
  rw [partialValue, Finset.sum_range]
  simp [binaryValue]

/-- Conditional binary powering from any uniform fixed-power circuit bound. -/
theorem synthesis_binary_powering (f : State n → State n) (C : ℕ)
    (hpowers : ∀ T, ∃ c : Circuit Boolean.signature n n,
      c.Computes Boolean.interpretation (f^[T]) ∧ c.size ≤ C)
    (s : Set (State w → Bool)) (init : State w → State n) (bits : State w → Fin m → Bool)
    (hi : wires init ⊆ s) (hb : ∀ j, (fun x => bits x j) ∈ s) :
    Synthesis Boolean.interpretation s
      (wires fun x => f^[binaryValue (bits x)] (init x))
      (m * (C + 4 * n)) := by
  let state := fun j x => f^[partialValue (bits x) j] (init x)
  let q := fun j => wires (state j)
  have hz : q 0 ⊆ s := by simpa [q, state] using hi
  have hstep (j : ℕ) (hj : j < m) :
      Synthesis Boolean.interpretation (s ∪ Synthesis.stages q j) (q (j + 1))
        (C + 4 * n) := by
    obtain ⟨pow, hp, hs⟩ := hpowers (2 ^ j)
    let src := s ∪ Synthesis.stages q j
    have hav : wires (state j) ⊆ src := fun _ h => Or.inr (Synthesis.mem_stages q j h)
    have hpow := Synthesis.circuit (I := Boolean.interpretation) (s := src) pow (state j)
      (fun bit => hav ⟨bit, rfl⟩)
    have hmux := synthesis_bits_mux
      (src ∪ wires fun x => pow.eval Boolean.interpretation (state j x))
      (fun x => pow.eval Boolean.interpretation (state j x)) (state j)
      (fun x => bits x ⟨j, hj⟩) (fun _ h => Or.inr h)
      (fun _ h => Or.inl (hav h)) (Or.inl (Or.inl (hb ⟨j, hj⟩)))
    have he : (fun x => if bits x ⟨j, hj⟩ then pow.eval Boolean.interpretation (state j x)
        else state j x) = state (j + 1) := by
      funext x
      rw [hp]
      dsimp [state]
      rw [partialValue_succ _ hj]
      split_ifs
      · rw [← Function.iterate_add_apply, Nat.add_comm]
      · simp
    have h := hpow.trans hmux
    rw [he] at h
    exact h.mono Set.Subset.rfl Set.Subset.rfl (Nat.add_le_add_right hs _)
  have h := Synthesis.steps q _ m hz hstep
  have hfinal := h.mono Set.Subset.rfl (Synthesis.mem_stages q m) le_rfl
  simpa [q, state] using hfinal

/-- An `m`-bit time input multiplies a fixed-power bound by at most `m`, including
the conditional-selection cost at each stage. -/
theorem binary_powering_circuit (f : State n → State n) (C m : ℕ)
    (hpowers : ∀ T, ∃ c : Circuit Boolean.signature n n,
      c.Computes Boolean.interpretation (f^[T]) ∧ c.size ≤ C) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      out.Computes Boolean.interpretation (fun x =>
        f^[binaryValue (fun j => x (Fin.natAdd n j))]
          (fun i => x (Fin.castAdd m i))) ∧ out.size ≤ m * (C + 4 * n) :=
  (synthesis_binary_powering f C hpowers (inputs (n + m))
    (fun x i => x (Fin.castAdd m i)) (fun x j => x (Fin.natAdd n j))
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) (fun j => ⟨_, rfl⟩)).exists_circuit_outputs

/-- Conditional checkpoint powers, retaining the time input and current state. -/
theorem synthesis_variable_time (c : Circuit Boolean.signature n n)
    (s : Set (State w → Bool)) (init : State w → State n) (bits : State w → Fin m → Bool)
    (hi : wires init ⊆ s) (hb : ∀ j, (fun x => bits x j) ∈ s)
    (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    Synthesis Boolean.interpretation s
      (wires fun x => (c.eval Boolean.interpretation)^[binaryValue (bits x)] (init x))
      (m * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n)) :=
  synthesis_binary_powering _ _ (fun T => fixed_power n c T L hL hLN) s init bits hi hb

/-- An explicit integer tradeoff for an `m`-bit input exponent. -/
theorem variable_time (c : Circuit Boolean.signature n n) (m L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ x, out.eval Boolean.interpretation x =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => x (Fin.natAdd n j))]
          (fun i => x (Fin.castAdd m i))) ∧
      out.size ≤ m * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n) := by
  exact (synthesis_variable_time c (inputs (n + m))
    (fun x i => x (Fin.castAdd m i)) (fun x j => x (Fin.natAdd n j))
    (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) (fun j => ⟨_, rfl⟩) L hL hLN).exists_circuit_outputs

theorem variable_time_optimized (c : Circuit Boolean.signature n n) (m : ℕ) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ x, out.eval Boolean.interpretation x =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => x (Fin.natAdd n j))]
          (fun i => x (Fin.castAdd m i))) ∧
      (out.size : ℝ) ≤ m * (120000 * optimizedBudget n c.size (2 ^ n) + 4 * n) := by
  obtain ⟨L, hL, hLN, ho⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := variable_time c m L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ m * (40000 * (powerBudget n c.size (2 ^ n) L : ℝ) + 4 * n) := by
    exact_mod_cast hs
  exact hs'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end IteratedFunctions
