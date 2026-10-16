/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Synthesis
public import Init.Data.BitVec.Bitblast
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Bounded-word arithmetic

The arithmetic semantics are Lean's `BitVec` operations. Their bit-blasting
identities supply the proof; CSLib synthesis supplies the gate counts. No
native evaluation or decision-procedure axiom is used.
-/

@[expose] public section

namespace Cslib.Circuits.Synthesis

variable {n : ℕ} {s : Set ((Fin n → Bool) → Bool)}
variable {f g : (Fin n → Bool) → Bool} {a b : ℕ}

/-- XOR with an explicit bound, including its argument constructions. -/
theorem xor (hf : Synthesis Boolean.interpretation s {f} a)
    (hg : Synthesis Boolean.interpretation s {g} b) :
    Synthesis Boolean.interpretation s {fun x => f x ^^ g x} (2 * a + 2 * b + 5) := by
  have h := (hf.and hg.not).or (hf.not.and hg)
  have heq : (fun x => f x && !g x || !f x && g x) = (fun x => f x ^^ g x) := by
    funext x
    cases f x <;> cases g x <;> rfl
  convert h using 1
  · rw [heq]
  · lia

end Cslib.Circuits.Synthesis

namespace IteratedFunctions

open Cslib.Circuits

variable {n w : ℕ} (s : Set ((Fin n → Bool) → Bool))
variable (a b : (Fin n → Bool) → BitVec w)
variable (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
variable (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s)

include ha hb

/-- One carry chain uses a constant number of gates per bit. -/
theorem synthesis_carry (c : Bool) (t : ℕ) (ht : t ≤ w) :
    Synthesis Boolean.interpretation s {fun x => BitVec.carry t (a x) (b x) c} (4 * t + 1) := by
  induction t with
  | zero => simpa using Synthesis.const c
  | succ t ih =>
    have hc := ih (by lia)
    have h := ((Synthesis.of_mem (ha ⟨t, by lia⟩)).and (Synthesis.of_mem (hb ⟨t, by lia⟩))).or
      (((Synthesis.of_mem (ha ⟨t, by lia⟩)).or (Synthesis.of_mem (hb ⟨t, by lia⟩))).and hc)
    have heq : (fun x => (a x).getLsbD t && (b x).getLsbD t ||
        ((a x).getLsbD t || (b x).getLsbD t) && BitVec.carry t (a x) (b x) c) =
        (fun x => BitVec.carry (t + 1) (a x) (b x) c) := by
      funext x
      rw [BitVec.carry_succ]
      cases (a x).getLsbD t <;> cases (b x).getLsbD t <;>
        cases BitVec.carry t (a x) (b x) c <;> rfl
    convert h using 1
    · rw [heq]
    · lia

/-- Simultaneous addition; the deliberately loose quadratic bound is sufficient here. -/
theorem synthesis_add :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun x => (a x + b x).getLsbD i.val) (40 * (w + 1) ^ 2) := by
  have hs := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun i : Fin w => fun x => (a x + b x).getLsbD i.val)
    (fun _ => 40 * (w + 1)) (fun i => ?_)
  · exact hs.mono Set.Subset.rfl Set.Subset.rfl (by simp; nlinarith)
  · have h := (Synthesis.of_mem (ha i)).xor
      ((Synthesis.of_mem (hb i)).xor (synthesis_carry s a b ha hb false i.val i.isLt.le))
    have heq : (fun x => (a x + b x).getLsbD i.val) =
        (fun x => (a x).getLsbD i.val ^^
          ((b x).getLsbD i.val ^^ BitVec.carry i.val (a x) (b x) false)) :=
      funext fun x => BitVec.getLsbD_add i.isLt (a x) (b x)
    rw [heq]
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by have := i.isLt; lia)

/-- Addition with an initial carry; used for two's-complement subtraction. -/
theorem synthesis_addCarry (c : Bool) :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun x =>
        (a x + b x + BitVec.setWidth w (BitVec.ofBool c)).getLsbD i.val)
      (40 * (w + 1) ^ 2) := by
  have hs := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun i : Fin w => fun x =>
      (a x + b x + BitVec.setWidth w (BitVec.ofBool c)).getLsbD i.val)
    (fun _ => 40 * (w + 1)) (fun i => ?_)
  · exact hs.mono Set.Subset.rfl Set.Subset.rfl (by simp; nlinarith)
  · have h := (Synthesis.of_mem (ha i)).xor
      ((Synthesis.of_mem (hb i)).xor (synthesis_carry s a b ha hb c i.val i.isLt.le))
    have heq : (fun x => (a x + b x + BitVec.setWidth w (BitVec.ofBool c)).getLsbD i.val) =
        (fun x => (a x).getLsbD i.val ^^
          ((b x).getLsbD i.val ^^ BitVec.carry i.val (a x) (b x) c)) :=
      funext fun x => BitVec.getLsbD_add_add_bool i.isLt (a x) (b x) c
    rw [heq]
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by have := i.isLt; lia)

omit ha hb in
/-- A hardwired word uses at most one constant gate per bit. -/
theorem synthesis_word_const (v : BitVec w) :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun _ => v.getLsbD i.val) w := by
  simpa using Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun i : Fin w => fun _ => v.getLsbD i.val) (fun _ => 1) (fun i => Synthesis.const _)

omit ha in
/-- Bitwise complementation. -/
theorem synthesis_word_not :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun x => (~~~b x).getLsbD i.val) w := by
  have h := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun i : Fin w => fun x => !(b x).getLsbD i.val) (fun _ => 1)
    (fun i => (Synthesis.of_mem (hb i)).not)
  simpa only [BitVec.getLsbD_not, Fin.is_lt, decide_true, Bool.true_and,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

/-- Unsigned comparison, using a complemented carry chain. -/
theorem synthesis_ult :
    Synthesis Boolean.interpretation s {fun x => (a x).ult (b x)} (5 * w + 2) := by
  have hn := synthesis_word_not s b hb
  have hc := synthesis_carry (s ∪ Set.range (fun i : Fin w => fun x => (~~~b x).getLsbD i.val))
    a (fun x => ~~~b x) (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true w le_rfl
  have h := hn.trans hc.not
  simpa only [BitVec.ult_eq_not_carry, Nat.mul_succ, Nat.add_assoc,
    show w + (4 * w + 1 + 1) = 5 * w + 2 by lia] using h

/-- Subtraction modulo the word width, with a quadratic gate bound. -/
theorem synthesis_sub :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun x => (a x - b x).getLsbD i.val)
      (41 * (w + 1) ^ 2) := by
  have hn := synthesis_word_not s b hb
  have hc := synthesis_addCarry
    (s ∪ Set.range (fun i : Fin w => fun x => (~~~b x).getLsbD i.val))
    a (fun x => ~~~b x) (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true
  have h := hn.trans hc
  have heq (x : Fin n → Bool) :
      a x - b x = a x + ~~~b x + BitVec.setWidth w (BitVec.ofBool true) := by
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  simp only [← heq] at h
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

/-- Word equality with a linear gate bound. -/
theorem synthesis_word_eq :
    Synthesis Boolean.interpretation s {fun x => decide (a x = b x)} (6 * w + 1) := by
  have h := Synthesis.forall_mem (s := s) Finset.univ
    (fun i : Fin w => fun x => decide ((a x).getLsbD i.val = (b x).getLsbD i.val))
    (fun _ => 5) (fun i _ => Synthesis.bool_eq (ha i) (hb i))
  have heq (x : Fin n → Bool) :
      (∀ i : Fin w, (a x).getLsbD i.val = (b x).getLsbD i.val) ↔ a x = b x := by
    constructor
    · intro hbits
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      exact hbits ⟨i, hi⟩
    · intro h
      simp only [h, implies_true]
  simpa only [Finset.mem_univ, forall_true_left, decide_eq_true_eq, heq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

omit ha hb in
/-- A word-wide multiplexer shares the available control bit. -/
theorem synthesis_word_mux (flag : (Fin n → Bool) → Bool) (hf : flag ∈ s)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis Boolean.interpretation s
      (Set.range fun i : Fin w => fun x =>
        (if flag x then a x else b x).getLsbD i.val) (4 * w) := by
  have h := Synthesis.family (I := Boolean.interpretation) (s := s)
    (fun i : Fin w => fun x => if flag x then (a x).getLsbD i.val else (b x).getLsbD i.val)
    (fun _ => 4) (fun i => Synthesis.mux hf (ha i) (hb i))
  have heq : (fun i : Fin w => fun x => (if flag x then a x else b x).getLsbD i.val) =
      (fun i : Fin w => fun x => if flag x then (a x).getLsbD i.val else (b x).getLsbD i.val) := by
    funext i x
    split <;> rfl
  rw [heq]
  simpa [Nat.mul_comm] using h

end IteratedFunctions
