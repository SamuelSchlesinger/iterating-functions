/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Decoder
public import Proofs.RecordCircuits
import Mathlib.Tactic.Linarith

/-! # Gate bounds for the reconstruction circuit -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n w : ℕ}

theorem synthesis_ite {m A B F : ℕ} {s : Set (State n → Bool)}
    {a b : State n → Fin m → Bool} {flag : State n → Bool}
    (ha : Synthesis Boolean.interpretation s (wires a) A)
    (hb : Synthesis Boolean.interpretation s (wires b) B)
    (hf : Synthesis Boolean.interpretation s {flag} F) :
    Synthesis Boolean.interpretation s (wires fun x => if flag x then a x else b x)
      (A + B + F + 4 * m) := by
  exact ((ha.union hb).union hf).trans (synthesis_bits_mux _ a b flag
    (fun _ h => Or.inr (Or.inl (Or.inl h)))
    (fun _ h => Or.inr (Or.inl (Or.inr h))) (Or.inr (Or.inr rfl)))

def prefixWires (f : State n → State n) (K : ℕ) : Set (State n → Bool) :=
  Synthesis.stages (fun j => wires fun x => f^[j] x) K

theorem prefix_mem (f : State n → State n) {K j : ℕ} (hj : j ≤ K) (bit : Fin n) :
    (fun x => f^[j] x bit) ∈ prefixWires f K := by
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by lia), ⟨bit, rfl⟩⟩⟩

theorem synthesis_repeatedValue (s : Set (State n → Bool)) (f : State n → State n)
    (T K : ℕ) (lo hi : State n → BitVec w)
    (hlo : ∀ i : Fin w, (fun x => (lo x).getLsbD i.val) ∈ s)
    (hhi : ∀ i : Fin w, (fun x => (hi x).getLsbD i.val) ∈ s)
    (hp : prefixWires f K ⊆ s) (hc : ∀ b : Bool, (fun _ : State n => b) ∈ s) :
    Synthesis Boolean.interpretation s (wires fun x => repeatedValue f T K x (lo x) (hi x))
      (200 * (K + 1) * (n + w + 1) ^ 2) := by
  have hidx := synthesis_repeatWordIndex s T K lo hi hlo hhi hc
  have hsel := synthesis_selectBits (s ∪ wordWires fun x => repeatWordIndex T K (lo x) (hi x))
    (fun x => repeatWordIndex T K (lo x) (hi x)) (fun j : Fin (K + 1) => fun x => f^[j.val] x)
    (fun i => Or.inr ⟨i, rfl⟩)
    (fun j bit => Or.inl (hp (prefix_mem f (by have := j.isLt; lia) bit)))
  apply (hidx.trans hsel).mono Set.Subset.rfl Set.Subset.rfl
  nlinarith [Nat.zero_le (K * n ^ 2), Nat.zero_le (K * n * w), Nat.zero_le (K * w ^ 2)]

theorem synthesis_hitValue (s : Set (State n → Bool)) (c : Circuit Boolean.signature n n)
    (K : ℕ) (index : State n → BitVec w) (payload : State n → State n)
    (hi : ∀ i : Fin w, (fun x => (index x).getLsbD i.val) ∈ s)
    (hp : wires payload ⊆ s) (hc : ∀ b : Bool, (fun _ : State n => b) ∈ s) :
    Synthesis Boolean.interpretation s
      (wires fun x => hitValue (c.eval Boolean.interpretation) K (index x) (payload x))
      (K * c.size + 200 * (K + 1) * (n + w + 1) ^ 2) := by
  let idx := fun x => BitVec.ofNat w K - index x
  let trace := Synthesis.stages
    (fun j => wires fun x => (c.eval Boolean.interpretation)^[j] (payload x)) K
  have horbit := synthesis_orbit Boolean.interpretation c s payload (fun i => hp ⟨i, rfl⟩) K
  have hidx := synthesis_sub s (fun _ => BitVec.ofNat w K) index (fun _ => hc _) hi
  have hsel := synthesis_selectBits (s ∪ (trace ∪ wordWires idx)) idx
    (fun j : Fin (K + 1) => fun x => (c.eval Boolean.interpretation)^[j.val] (payload x))
    (fun i => Or.inr (Or.inr ⟨i, rfl⟩)) (fun j bit => ?_)
  · apply ((horbit.union hidx).trans hsel).mono Set.Subset.rfl Set.Subset.rfl
    nlinarith [Nat.zero_le (K * n ^ 2), Nat.zero_le (K * n * w), Nat.zero_le (K * w ^ 2)]
  · exact Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j.val,
      Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr j.isLt, ⟨bit, rfl⟩⟩⟩))

theorem synthesis_reconstruct (s : Set (State n → Bool)) (c : Circuit Boolean.signature n n)
    (T K : ℕ) (a b : State n → Record n w)
    (ha : Record.wireSet a ⊆ s) (hb : Record.wireSet b ⊆ s)
    (hp : prefixWires (c.eval Boolean.interpretation) K ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State n => b) ∈ s) :
    Synthesis Boolean.interpretation s
      (wires fun x => reconstruct (c.eval Boolean.interpretation) T K x (a x) (b x))
      (4 * K * c.size + 1000 * (K + 1) * (n + w + 1) ^ 2) := by
  have hleft := synthesis_hitValue s c K (fun x => (b x).index) (fun x => (a x).payload)
    (Record.index_mem s b hb) (by rintro _ ⟨i, rfl⟩; exact Record.payload_mem s a ha i) hc
  have hright := synthesis_hitValue s c K (fun x => (a x).index) (fun x => (b x).payload)
    (Record.index_mem s a ha) (by rintro _ ⟨i, rfl⟩; exact Record.payload_mem s b hb i) hc
  have hforward := synthesis_repeatedValue s (c.eval Boolean.interpretation) T K
    (fun x => (a x).index) (fun x => (b x).index)
    (Record.index_mem s a ha) (Record.index_mem s b hb) hp hc
  have hbackward := synthesis_repeatedValue s (c.eval Boolean.interpretation) T K
    (fun x => (b x).index) (fun x => (a x).index)
    (Record.index_mem s b hb) (Record.index_mem s a ha) hp hc
  have hcmp := synthesis_ult s (fun x => (a x).index) (fun x => (b x).index)
    (Record.index_mem s a ha) (Record.index_mem s b hb)
  have h := synthesis_ite hleft (synthesis_ite hright
    (synthesis_ite hforward hbackward hcmp) (Synthesis.of_mem (Record.checkpoint_mem s b hb)))
    (Synthesis.of_mem (Record.checkpoint_mem s a ha))
  apply h.mono Set.Subset.rfl Set.Subset.rfl
  nlinarith [Nat.zero_le (K * c.size)]

end IteratedFunctions
