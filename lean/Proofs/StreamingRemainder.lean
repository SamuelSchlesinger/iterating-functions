/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.LinearArithmetic
public import Proofs.BinaryNumbers
import Mathlib.Tactic.Linarith

/-!
# Linear cost per input bit for a bounded-modulus remainder

The input time can be much wider than the modulus. One spare arithmetic bit
ensures that doubling a valid remainder never overflows. This is the arithmetic
ingredient for additive dependence on live-time width.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n w m : ℕ}

def remainderStep (d r : BitVec w) (b : Bool) : BitVec w :=
  let next := r.shiftConcat b
  if next.ult d then next else next - d

def streamRemainder (d : BitVec w) : {m : ℕ} → (Fin m → Bool) → BitVec w
  | 0, _ => 0
  | _ + 1, bits => remainderStep d (streamRemainder d (fun i => bits i.succ)) (bits 0)

theorem binaryValue_cons (bits : Fin (m + 1) → Bool) :
    binaryValue bits = 2 * binaryValue (fun i => bits i.succ) + (bits 0).toNat := by
  unfold binaryValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, Nat.mul_comm,
    mul_ite, mul_zero, Finset.mul_sum]
  cases bits 0 <;> simp [Nat.add_comm]

theorem remainderStep_toNat (d r : BitVec w) (b : Bool)
    (hd : 0 < d.toNat) (hw : 2 * d.toNat ≤ 2 ^ w) (hr : r.toNat < d.toNat) :
    (remainderStep d r b).toNat = (2 * r.toNat + b.toNat) % d.toNat := by
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have hfit : 2 * r.toNat + b.toNat < 2 ^ w := by lia
  have hs : (r.shiftConcat b).toNat = 2 * r.toNat + b.toNat := by
    simp only [BitVec.toNat_shiftConcat, Nat.shiftLeft_eq, pow_one]
    rw [Nat.mul_comm r.toNat 2, Nat.mod_eq_of_lt hfit]
  unfold remainderStep
  simp only [BitVec.ult, hs, decide_eq_true_eq]
  split_ifs with ht
  · rw [hs, Nat.mod_eq_of_lt ht]
  · have hle : d ≤ r.shiftConcat b := by change d.toNat ≤ _; rw [hs]; lia
    rw [BitVec.toNat_sub_of_le hle, hs, Nat.mod_eq_sub_mod (by lia)]
    exact (Nat.mod_eq_of_lt (by lia)).symm

/-- Exact remainder semantics for little-endian input bits and a nonzero bounded modulus. -/
theorem streamRemainder_toNat (d : BitVec w) (bits : Fin m → Bool)
    (hd : 0 < d.toNat) (hw : 2 * d.toNat ≤ 2 ^ w) :
    (streamRemainder d bits).toNat = binaryValue bits % d.toNat := by
  induction m with
  | zero => simp [streamRemainder, binaryValue]
  | succ m ih =>
    rw [streamRemainder, remainderStep_toNat d _ _ hd hw
      (by rw [ih]; exact Nat.mod_lt _ hd), ih, binaryValue_cons]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem synthesis_remainderStep (s : Set (State n → Bool))
    (d r : State n → BitVec w) (b : State n → Bool)
    (hd : ∀ i : Fin w, (fun x => (d x).getLsbD i.val) ∈ s)
    (hr : ∀ i : Fin w, (fun x => (r x).getLsbD i.val) ∈ s) (hb : b ∈ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => remainderStep (d x) (r x) (b x)) (51 * w + 4) := by
  let next := fun x => (r x).shiftConcat (b x)
  have hn (i : Fin w) : (fun x => (next x).getLsbD i.val) ∈ s := by
    by_cases hi : i.val = 0
    · simpa only [next, hi, BitVec.getLsbD_shiftConcat, show 0 < w by have := i.isLt; lia,
        ite_true, decide_true, Bool.true_and] using hb
    · simpa only [next, BitVec.getLsbD_shiftConcat, Fin.is_lt, ite_true, hi, ite_false,
        decide_true, Bool.true_and] using hr ⟨i.val - 1, by have := i.isLt; lia⟩
  have hs := synthesis_sub_linear s next d hn hd
  have hl := synthesis_ult s next d hn hd
  let src := s ∪ (wordWires (fun x => next x - d x) ∪ {fun x => (next x).ult (d x)})
  have hm := synthesis_word_mux src next (fun x => next x - d x)
    (fun x => (next x).ult (d x)) (Or.inr (Or.inr rfl))
    (fun i => Or.inl (hn i)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
  exact ((hs.union hl).trans hm).mono Set.Subset.rfl Set.Subset.rfl (by lia)

/-- The modulus width, rather than the time width, determines each division stage's cost. -/
theorem synthesis_streamRemainder (s : Set (State n → Bool))
    (d : State n → BitVec w) (bits : State n → Fin m → Bool)
    (hd : ∀ i : Fin w, (fun x => (d x).getLsbD i.val) ∈ s)
    (hb : ∀ j, (fun x => bits x j) ∈ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => streamRemainder (d x) (bits x)) (1 + m * (51 * w + 4)) := by
  induction m with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero]
    apply (Synthesis.const (s := s) false).mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨i, rfl⟩
    simp [streamRemainder]
  | succ m ih =>
    have previous := ih (fun x i => bits x i.succ) (fun i => hb i.succ)
    have step := synthesis_remainderStep
      (s ∪ wordWires (fun x => streamRemainder (d x) (fun i : Fin m => bits x i.succ)))
      d (fun x => streamRemainder (d x) (fun i : Fin m => bits x i.succ)) (fun x => bits x 0)
      (fun i => Or.inl (hd i)) (fun i => Or.inr ⟨i, rfl⟩) (Or.inl (hb 0))
    exact (previous.trans step).mono Set.Subset.rfl Set.Subset.rfl (by lia)

/-- An `m`-bit numerator modulo a nonzero `k`-bit modulus in `O(m(k+1))` gates.
The circuit is total; the remainder specification requires a nonzero modulus. -/
theorem bounded_modulus_remainder (m k : ℕ) :
    ∃ out : Circuit Boolean.signature (m + k) k,
      (∀ x, let d := word (fun i => x (Fin.natAdd m i))
        0 < d.toNat → (word (out.eval Boolean.interpretation x)).toNat =
          binaryValue (fun i => x (Fin.castAdd k i)) % d.toNat) ∧
      out.size ≤ 2 + m * (51 * (k + 1) + 4) := by
  let d := fun x : State (m + k) => word (fun i => x (Fin.natAdd m i))
  let bits := fun x : State (m + k) => fun i : Fin m => x (Fin.castAdd k i)
  let wide := fun x => (d x).setWidth (k + 1)
  let src := inputs (m + k) ∪ {fun _ : State (m + k) => false}
  have hz : (fun _ : State (m + k) => false) ∈ src := Or.inr rfl
  have hd : wordWires d ⊆ src := by
    rintro _ ⟨i, rfl⟩
    simpa only [d, word_bit] using
      (show (fun x : State (m + k) => x (Fin.natAdd m i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hw := resize_wires (v := k + 1) src d hd hz
  have hs := synthesis_streamRemainder src wide bits (fun i => hw ⟨i, rfl⟩)
    (fun i => Or.inl ⟨_, rfl⟩)
  let result := fun x => streamRemainder (wide x) (bits x)
  have hout := resize_wires (v := k) (src ∪ wordWires result) result
    (fun _ h => Or.inr h) (Or.inl hz)
  have hc := (Synthesis.const (s := inputs (m + k)) false).trans
    (hs.trans (Synthesis.of_subset hout))
  obtain ⟨out, ho, hsize⟩ := hc.exists_circuit_outputs
  refine ⟨out, fun x hpos => ?_, by lia⟩
  have hdn : (wide x).toNat = (d x).toNat := by
    simp only [wide, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt ((d x).isLt.trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ k)))
  have hb : 2 * (wide x).toNat ≤ 2 ^ (k + 1) := by
    rw [hdn, pow_succ]
    have := (d x).isLt
    lia
  have hr := streamRemainder_toNat (wide x) (bits x) (by simpa only [hdn] using hpos) hb
  rw [hdn] at hr
  rw [ho x, word_bits, BitVec.toNat_setWidth]
  rw [hr, Nat.mod_eq_of_lt ((Nat.mod_lt _ hpos).trans (d x).isLt)]

end IteratedFunctions
