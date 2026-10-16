/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.RecordCircuits
public import Proofs.Arithmetic
import Mathlib.Tactic.Linarith

/-! # A cubic gate bound for variable-modulus remainder -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n w : ℕ}

theorem divRec_eq_iterate (j : ℕ) (args : BitVec.DivModArgs w) (qr : BitVec.DivModState w) :
    BitVec.divRec j args qr = (BitVec.divSubtractShift args)^[j] qr := by
  induction j generalizing qr with
  | zero => rfl
  | succ j ih => rw [BitVec.divRec_succ, ih, Function.iterate_succ_apply]

theorem division_wn (j : ℕ) (args : BitVec.DivModArgs w) :
    ((BitVec.divSubtractShift args)^[j] (BitVec.DivModState.init w)).wn = w - j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simp only [BitVec.divSubtractShift]
    split <;> dsimp only <;> rw [ih] <;> lia

/-- Long division with fixed word width; subtraction is charged its existing quadratic cost. -/
theorem synthesis_umod (s : Set (State n → Bool)) (a b : State n → BitVec w)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis Boolean.interpretation s (wordWires fun x => a x % b x)
      (100 * (w + 1) ^ 3) := by
  let args := fun x => ({n := a x, d := b x} : BitVec.DivModArgs w)
  let state := fun j x => (BitVec.divSubtractShift (args x))^[j] (BitVec.DivModState.init w)
  let q := fun j => wordWires fun x => (state j x).r
  let constants : Set (State n → Bool) := {fun _ => false, fun _ => true}
  let src := s ∪ constants
  have hc (v : Bool) : (fun _ : State n => v) ∈ src := by
    cases v <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation s constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hz : q 0 ⊆ src := by
    rintro _ ⟨bit, rfl⟩
    simpa [state, BitVec.DivModState.init] using hc false
  have hstep (j : ℕ) (hj : j < w) :
      Synthesis Boolean.interpretation (src ∪ Synthesis.stages q j) (q (j + 1))
        (60 * (w + 1) ^ 2) := by
    let src1 := src ∪ Synthesis.stages q j
    let shifted := fun x => (state j x).r.shiftConcat ((a x).getLsbD (w - j - 1))
    have hav (i : Fin w) : (fun x => (state j x).r.getLsbD i.val) ∈ src1 :=
      Or.inr (Synthesis.mem_stages q j ⟨i, rfl⟩)
    have hshift (i : Fin w) : (fun x => (shifted x).getLsbD i.val) ∈ src1 := by
      by_cases hi : i.val = 0
      · simpa only [shifted, hi, BitVec.getLsbD_shiftConcat, Fin.is_lt,
          ite_true, show 0 < w by lia, decide_true, Bool.true_and] using
          (show (fun x => (a x).getLsbD (w - j - 1)) ∈ src1 from
            Or.inl (Or.inl (ha ⟨w - j - 1, by lia⟩)))
      · simpa only [shifted, BitVec.getLsbD_shiftConcat, Fin.is_lt, ite_true, hi, ite_false,
          decide_true, Bool.true_and]
          using hav ⟨i.val - 1, by have := i.isLt; lia⟩
    have hsub := synthesis_sub src1 shifted b hshift (fun i => Or.inl (Or.inl (hb i)))
    have hlt := synthesis_ult src1 shifted b hshift (fun i => Or.inl (Or.inl (hb i)))
    let src2 := src1 ∪ (wordWires (fun x => shifted x - b x) ∪ {fun x => (shifted x).ult (b x)})
    have hm := synthesis_word_mux src2 shifted (fun x => shifted x - b x)
      (fun x => (shifted x).ult (b x)) (Or.inr (Or.inr rfl))
      (fun i => Or.inl (hshift i)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
    have he (x : State n) : (if (shifted x).ult (b x) then shifted x else shifted x - b x) =
        (state (j + 1) x).r := by
      simp only [state, Function.iterate_succ_apply', BitVec.divSubtractShift, args,
        division_wn, shifted, BitVec.ult, BitVec.lt_def, decide_eq_true_eq]
      split <;> rfl
    have h := (hsub.union hlt).trans hm
    simp only [he] at h
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)
  have hd := Synthesis.steps q (60 * (w + 1) ^ 2) w hz hstep
  let src1 := src ∪ Synthesis.stages q w
  have hzero := synthesis_word_eq_const src1 b (fun i => Or.inl (Or.inl (hb i))) 0
  let src2 := src1 ∪ {fun x => decide (b x = 0)}
  have hm := synthesis_word_mux src2 a (fun x => (state w x).r)
    (fun x => decide (b x = 0)) (Or.inr rfl)
    (fun i => Or.inl (Or.inl (Or.inl (ha i))))
    (fun i => Or.inl (Or.inr (Synthesis.mem_stages q w ⟨i, rfl⟩)))
  have he (x : State n) : (if decide (b x = 0) then a x else (state w x).r) = a x % b x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_umod, divRec_eq_iterate]
    dsimp only [state, args]
    simp only [decide_eq_true_eq, BitVec.ofNat_eq_ofNat]
    split_ifs <;> rfl
  have h := hconst.trans (hd.trans (hzero.trans hm))
  simp only [he] at h
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

end IteratedFunctions
