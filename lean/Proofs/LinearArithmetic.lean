/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Arithmetic
public import Statement

/-! # Linear-size word addition using shared carries -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n w : ℕ}

theorem synthesis_add_linear (s : Set (State n → Bool))
    (a b : State n → BitVec w)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun x => (a x + b x).getLsbD i.val) (20 * w + 1) := by
  let q := fun j => ({fun x => BitVec.carry j (a x) (b x) false} : Set (State n → Bool))
  let s0 := s ∪ {fun _ : State n => false}
  have hzero : q 0 ⊆ s0 := by simp [q, s0]
  have hstep (j : ℕ) (hj : j < w) :
      Synthesis Boolean.interpretation (s0 ∪ Synthesis.stages q j) (q (j + 1)) 4 := by
    let src := s0 ∪ Synthesis.stages q j
    have hcarry : (fun x => BitVec.carry j (a x) (b x) false) ∈ src :=
      Or.inr (Synthesis.mem_stages q j rfl)
    have h := ((Synthesis.of_mem (s := src) (Or.inl (Or.inl (ha ⟨j, hj⟩)))).and
      (Synthesis.of_mem (Or.inl (Or.inl (hb ⟨j, hj⟩))))).or
      (((Synthesis.of_mem (Or.inl (Or.inl (ha ⟨j, hj⟩)))).or
        (Synthesis.of_mem (Or.inl (Or.inl (hb ⟨j, hj⟩))))).and (Synthesis.of_mem hcarry))
    have he : (fun x => (a x).getLsbD j && (b x).getLsbD j ||
        ((a x).getLsbD j || (b x).getLsbD j) && BitVec.carry j (a x) (b x) false) =
        (fun x => BitVec.carry (j + 1) (a x) (b x) false) := by
      funext x
      rw [BitVec.carry_succ]
      cases (a x).getLsbD j <;> cases (b x).getLsbD j <;>
        cases BitVec.carry j (a x) (b x) false <;> rfl
    simpa only [he, q] using h
  have carries := Synthesis.steps q 4 w hzero hstep
  let src := s0 ∪ Synthesis.stages q w
  have hsum := Synthesis.family (I := Boolean.interpretation) (s := src)
    (fun i : Fin w => fun x => (a x + b x).getLsbD i.val) (fun _ => 15) (fun i => ?_)
  · have h := (Synthesis.const (s := s) false).trans (carries.trans hsum)
    apply h.mono Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    lia
  · have hc : (fun x => BitVec.carry i.val (a x) (b x) false) ∈ src :=
      Or.inr (Set.mem_iUnion.mpr ⟨i.val, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (by have := i.isLt; lia), rfl⟩⟩)
    have h := (Synthesis.of_mem (Or.inl (Or.inl (ha i)))).xor
      ((Synthesis.of_mem (Or.inl (Or.inl (hb i)))).xor (Synthesis.of_mem hc))
    have he := funext fun x => BitVec.getLsbD_add i.isLt (a x) (b x)
    simpa only [← he] using h

/-- Two's-complement subtraction with shared carry chains throughout. -/
theorem synthesis_sub_linear (s : Set (State n → Bool))
    (a b : State n → BitVec w)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun x => (a x - b x).getLsbD i.val) (42 * w + 2) := by
  have hn := synthesis_word_not s b hb
  have hsum := synthesis_add_linear (s ∪ Set.range
    (fun i : Fin w => fun x => (~~~b x).getLsbD i.val)) a (fun x => ~~~b x)
    (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩)
  have hone := synthesis_word_const
    (s ∪ Set.range (fun i : Fin w => fun x => (a x + ~~~b x).getLsbD i.val))
    (1 : BitVec w)
  have hout := synthesis_add_linear
    ((s ∪ Set.range (fun i : Fin w => fun x => (a x + ~~~b x).getLsbD i.val)) ∪
      Set.range (fun i : Fin w => fun _ : State n => (1 : BitVec w).getLsbD i.val))
    (fun x => a x + ~~~b x) (fun _ => 1)
    (fun i => Or.inl (Or.inr ⟨i, rfl⟩)) (fun i => Or.inr ⟨i, rfl⟩)
  have he (x : State n) : a x + ~~~b x + 1 = a x - b x := by
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
    congr 2
  have h := (hn.trans hsum).trans (hone.trans hout)
  simp only [he] at h
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by lia)

end IteratedFunctions
