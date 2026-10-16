/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ModulusCounter

/-! # A linear-size circuit for the explicit modular-counter permutation -/

@[expose] public section

namespace IteratedFunctions.ModulusCounter

open Cslib.Circuits

variable {k : ℕ}

def stepValue (a b : BitVec k) : BitVec k :=
  if b.ult a then if b + 1 = a then 0 else b + 1 else b

theorem stepValue_spec (a b : BitVec k) :
    stepValue a b = BitVec.ofNat k (advance a.toNat b.toNat 1) := by
  by_cases h : b.toNat < a.toNat
  · have ha : 0 < a.toNat := by lia
    have hs : b.toNat + 1 < 2 ^ k := by have := a.isLt; lia
    have hn : 1 < 2 ^ k := by have := a.isLt; lia
    have hsum : (b + 1).toNat = b.toNat + 1 := by
      simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hs]
    have he : b + 1 = a ↔ b.toNat + 1 = a.toNat := by
      rw [← BitVec.toNat_inj, hsum]
    simp only [stepValue, BitVec.ult, decide_eq_true_eq, h, ite_true, he, advance,
      ha, and_self]
    split_ifs with heq
    · apply BitVec.eq_of_toNat_eq
      simp [heq]
    · have hlt : b.toNat + 1 < a.toNat := by lia
      apply BitVec.eq_of_toNat_eq
      simp only [hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hs]
  · simp only [stepValue, BitVec.ult, decide_eq_true_eq, h, ite_false, advance,
      and_false]
    simp

/-- Native constants count as gates; no arithmetic operations are taken as primitives. -/
theorem exists_linear_circuit (k : ℕ) :
    ∃ c : Circuit Boolean.signature (k + k) (k + k),
      c.Computes Boolean.interpretation (power (k := k) 1) ∧ c.size ≤ 50 * (k + 1) := by
  let a := fun x : State (k + k) => leftWord x
  let b := fun x : State (k + k) => rightWord x
  let constants : Set (State (k + k) → Bool) := {fun _ => false, fun _ => true}
  let src := inputs (k + k) ∪ constants
  have hc (v : Bool) : (fun _ : State (k + k) => v) ∈ src := by
    cases v <;> simp [src, constants]
  have ha (i : Fin k) : (fun x => (a x).getLsbD i.val) ∈ src := by
    simpa only [a, leftWord, word_bit] using
      (show (fun x : State (k + k) => x (Fin.castAdd k i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hb (i : Fin k) : (fun x => (b x).getLsbD i.val) ∈ src := by
    simpa only [b, rightWord, word_bit] using
      (show (fun x : State (k + k) => x (Fin.natAdd k i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hconst : Synthesis Boolean.interpretation (inputs (k + k)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  let inc := fun x => b x + 1
  have hadd := synthesis_add_linear src b (fun _ => (1 : BitVec k)) hb (fun i => hc _)
  let src1 := src ∪ wordWires inc
  have hi (i : Fin k) : (fun x => (inc x).getLsbD i.val) ∈ src1 := Or.inr ⟨i, rfl⟩
  let equal := fun x => decide (inc x = a x)
  let active := fun x => (b x).ult (a x)
  have heq := synthesis_word_eq src1 inc a hi (fun i => Or.inl (ha i))
  have hlt := synthesis_ult src1 b a (fun i => Or.inl (hb i)) (fun i => Or.inl (ha i))
  let src2 := src1 ∪ ({equal} ∪ {active})
  let next := fun x => if equal x then (0 : BitVec k) else inc x
  have hm := synthesis_word_mux src2 (fun _ => (0 : BitVec k)) inc equal
    (Or.inr (Or.inl rfl)) (fun i => Or.inl (Or.inl (hc _))) (fun i => Or.inl (hi i))
  let src3 := src2 ∪ wordWires next
  have hm' := synthesis_word_mux src3 next b active
    (Or.inl (Or.inr (Or.inr rfl))) (fun i => Or.inr ⟨i, rfl⟩)
    (fun i => Or.inl (Or.inl (Or.inl (hb i))))
  have hout := hconst.trans (hadd.comp ((heq.union hlt).comp (hm.comp hm')))
  have hall := (Synthesis.of_subset (I := Boolean.interpretation)
    (s := inputs (k + k)) (t := inputs (k + k)) Set.Subset.rfl).union hout
  have hs : Synthesis Boolean.interpretation (inputs (k + k))
      (wires (power (k := k) 1)) (50 * (k + 1)) := by
    apply hall.mono Set.Subset.rfl ?_ (by lia)
    rintro _ ⟨bit, rfl⟩
    induction bit using Fin.addCases with
    | left i =>
      left
      exact ⟨Fin.castAdd k i, by
        funext x
        simp only [power, pack, Fin.append_left, leftWord, word_bit]⟩
    | right i =>
      right
      right
      right
      right
      refine ⟨i, ?_⟩
      funext x
      simp only [power, pack, Fin.append_right]
      rw [← stepValue_spec]
      simp only [stepValue, active, next, equal, inc, a, b, decide_eq_true_eq]
  obtain ⟨c, hcomp, hsize⟩ := hs.exists_circuit_outputs
  exact ⟨c, hcomp, hsize⟩

end IteratedFunctions.ModulusCounter
