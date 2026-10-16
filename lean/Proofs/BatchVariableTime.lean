/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.BatchPowers
public import Proofs.VariableTime

/-! # Independent input exponents with one dictionary per binary position -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
open scoped BigOperators

variable {n m r a : ℕ}

theorem synthesis_batched_variable_time (c : Circuit Boolean.signature n n)
    (s : Set (State a → Bool)) (init : State a → Fin r → State n)
    (bits : State a → Fin r → Fin m → Bool)
    (hi : ∀ member bit, (fun x => init x member bit) ∈ s)
    (hb : ∀ member j, (fun x => bits x member j) ∈ s)
    (hr : 0 < r) (hrN : r ≤ 2 ^ n) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    Synthesis Boolean.interpretation s
      (Set.range fun bit : Fin (r * n) => fun x =>
        let pair := (finProdFinEquiv (m := r) (n := n)).symm bit
        (c.eval Boolean.interpretation)^[binaryValue (bits x pair.1)] (init x pair.1) pair.2)
      (m * (1000000 * batchBudget n c.size (2 ^ n) r L + 4 * (r * n))) := by
  let f := c.eval Boolean.interpretation
  let state := fun j x member => f^[partialValue (bits x member) j] (init x member)
  let packed := fun j x bit =>
    let pair := (finProdFinEquiv (m := r) (n := n)).symm bit
    state j x pair.1 pair.2
  let q := fun j => wires (packed j)
  have hz : q 0 ⊆ s := by
    rintro _ ⟨bit, rfl⟩
    simpa [packed, state] using hi _ _
  have hstep (j : ℕ) (hj : j < m) :
      Synthesis Boolean.interpretation (s ∪ Synthesis.stages q j) (q (j + 1))
        (1000000 * batchBudget n c.size (2 ^ n) r L + 4 * (r * n)) := by
    obtain ⟨pow, hp, hs⟩ := batched_fixed_power c r (2 ^ j) L hr hrN hL hLN
    let src := s ∪ Synthesis.stages q j
    have hav : wires (packed j) ⊆ src := fun _ h => Or.inr (Synthesis.mem_stages q j h)
    have hpow := Synthesis.circuit (I := Boolean.interpretation) (s := src) pow (packed j)
      (fun bit => hav ⟨bit, rfl⟩)
    let output := fun x => pow.eval Boolean.interpretation (packed j x)
    let src' := src ∪ wires output
    let mixed := fun bit : Fin (r * n) => fun x =>
      let pair := (finProdFinEquiv (m := r) (n := n)).symm bit
      if bits x pair.1 ⟨j, hj⟩ then output x bit else packed j x bit
    have hmux : Synthesis Boolean.interpretation src' (Set.range mixed) (4 * (r * n)) := by
      have h := Synthesis.family (I := Boolean.interpretation) (s := src') mixed (fun _ => 4)
        (fun bit => Synthesis.mux (Or.inl (Or.inl (hb _ _))) (Or.inr ⟨bit, rfl⟩)
          (Or.inl (hav ⟨bit, rfl⟩)))
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul, Nat.mul_comm] using h
    have he : Set.range mixed = q (j + 1) := by
      congr 1
      funext bit x
      obtain ⟨⟨member, bit⟩, rfl⟩ := finProdFinEquiv.surjective bit
      simp only [mixed, packed, Equiv.symm_apply_apply, output, hp]
      dsimp only [state]
      rw [partialValue_succ _ hj]
      split_ifs
      · rw [← Function.iterate_add_apply, Nat.add_comm]
      · simp
    rw [he] at hmux
    exact (hpow.trans hmux).mono Set.Subset.rfl Set.Subset.rfl
      (Nat.add_le_add_right hs _)
  have h := Synthesis.steps q _ m hz hstep
  have hfinal := h.mono Set.Subset.rfl (Synthesis.mem_stages q m) le_rfl
  simpa only [q, packed, state, f, partialValue_all, wires] using hfinal

/-- Each member supplies its own initial state and its own little-endian exponent. -/
theorem batched_variable_time (c : Circuit Boolean.signature n n) (r m L : ℕ)
    (hr : 0 < r) (hrN : r ≤ 2 ^ n) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (r * (n + m)) (r * n),
      (∀ x member bit, out.eval Boolean.interpretation x (finProdFinEquiv (member, bit)) =
        (c.eval Boolean.interpretation)^[binaryValue
          (fun j => x (finProdFinEquiv (member, Fin.natAdd n j)))]
          (fun i => x (finProdFinEquiv (member, Fin.castAdd m i))) bit) ∧
      out.size ≤ m * (1000000 * batchBudget n c.size (2 ^ n) r L + 4 * (r * n)) := by
  obtain ⟨out, hout, hs⟩ := (synthesis_batched_variable_time c (inputs (r * (n + m)))
    (fun x member i => x (finProdFinEquiv (member, Fin.castAdd m i)))
    (fun x member j => x (finProdFinEquiv (member, Fin.natAdd n j)))
    (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩) hr hrN L hL hLN).exists_circuit_outputs
  refine ⟨out, ?_, hs⟩
  intro x member bit
  simpa only [Equiv.symm_apply_apply] using congrFun (hout x) (finProdFinEquiv (member, bit))

theorem batched_variable_time_optimized (c : Circuit Boolean.signature n n) (r m : ℕ)
    (hr : 0 < r) (hrN : r ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (r * (n + m)) (r * n),
      (∀ x member bit, out.eval Boolean.interpretation x (finProdFinEquiv (member, bit)) =
        (c.eval Boolean.interpretation)^[binaryValue
          (fun j => x (finProdFinEquiv (member, Fin.natAdd n j)))]
          (fun i => x (finProdFinEquiv (member, Fin.castAdd m i))) bit) ∧
      (out.size : ℝ) ≤ m *
        (3000000 * optimizedBatchBudget n c.size (2 ^ n) r + 4 * (r * n)) := by
  obtain ⟨L, hL, hLN, ho⟩ := batchBudget_optimized n c.size r hr
  obtain ⟨out, hout, hs⟩ := batched_variable_time c r m L hr hrN hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ m *
      (1000000 * (batchBudget n c.size (2 ^ n) r L : ℝ) + 4 * (r * n)) := by
    exact_mod_cast hs
  exact hs'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end IteratedFunctions
