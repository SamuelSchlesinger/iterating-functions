/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ModulusCounter
public import Proofs.StreamingRemainder

/-! # Fixed powers are equivalent to fixed-integer remainder functions -/

@[expose] public section

namespace IteratedFunctions.ModulusCounter

open Cslib.Circuits

variable {k n : ℕ}

/-- The zero-modulus branch is explicitly zero. -/
def remainder (T : ℕ) (x : State k) : State k :=
  fun i => (BitVec.ofNat k (if (word x).toNat = 0 then 0 else T % (word x).toNat)).getLsbD i.val

theorem remainder_word (T : ℕ) (x : State k) :
    word (remainder T x) =
      BitVec.ofNat k (if (word x).toNat = 0 then 0 else T % (word x).toNat) := word_bits _

/-- Retaining the carry bit is essential: two valid residues can overflow `k` bits. -/
def addResidue (a b r : BitVec k) : BitVec k :=
  let sum := b.setWidth (k + 1) + r.setWidth (k + 1)
  if b.ult a then
    (if sum.ult (a.setWidth (k + 1)) then sum else sum - a.setWidth (k + 1)).setWidth k
  else b

theorem addResidue_spec (a b r : BitVec k) (T : ℕ)
    (hr : 0 < a.toNat → r.toNat = T % a.toNat) :
    addResidue a b r = BitVec.ofNat k (advance a.toNat b.toNat T) := by
  have hwide (v : BitVec k) : (v.setWidth (k + 1)).toNat = v.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ k)))]
  by_cases h : b.toNat < a.toNat
  · have ha : 0 < a.toNat := by lia
    have hrlt : r.toNat < a.toNat := by rw [hr ha]; exact Nat.mod_lt _ ha
    have hfit : b.toNat + r.toNat < 2 ^ (k + 1) := by
      rw [pow_succ]
      have := a.isLt
      lia
    have hsum : (b.setWidth (k + 1) + r.setWidth (k + 1)).toNat = b.toNat + r.toNat := by
      rw [BitVec.toNat_add, hwide, hwide, Nat.mod_eq_of_lt hfit]
    have hmod : (b.toNat + r.toNat) % a.toNat = (b.toNat + T) % a.toNat := by
      rw [hr ha, Nat.add_mod_mod]
    unfold addResidue
    simp only [BitVec.ult, h, decide_true, ite_true, hsum, hwide, decide_eq_true_eq]
    split_ifs with hs
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, hsum, advance, ite_eq_left ⟨ha, h⟩, BitVec.toNat_ofNat,
        ← hmod, Nat.mod_eq_of_lt hs]
    · have hle : a.setWidth (k + 1) ≤ b.setWidth (k + 1) + r.setWidth (k + 1) := by
        change (a.setWidth (k + 1)).toNat ≤ _
        rw [hwide, hsum]
        lia
      have hsmall : b.toNat + r.toNat - a.toNat < a.toNat := by lia
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hle, hsum, hwide,
        advance, ite_eq_left ⟨ha, h⟩, BitVec.toNat_ofNat, ← hmod,
        Nat.mod_eq_sub_mod (show a.toNat ≤ b.toNat + r.toNat by lia), Nat.mod_eq_of_lt hsmall]
  · simp [addResidue, BitVec.ult, h, advance]

/-- Linear arithmetic and two selections, with a shared zero for widening. -/
theorem synthesis_addResidue (s : Set (State n → Bool)) (a b r : State n → BitVec k)
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) (hr : wordWires r ⊆ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun x => addResidue (a x) (b x) (r x)) (100 * (k + 1)) := by
  let s0 := s ∪ {fun _ : State n => false}
  have hz : (fun _ : State n => false) ∈ s0 := Or.inr rfl
  have hw (v : State n → BitVec k) (hv : wordWires v ⊆ s) :=
    resize_wires (v := k + 1) s0 v (fun _ h => Or.inl (hv h)) hz
  let sum := fun x => (b x).setWidth (k + 1) + (r x).setWidth (k + 1)
  let aw := fun x => (a x).setWidth (k + 1)
  have hadd := synthesis_add_linear s0 _ _
    (fun i => hw b hb ⟨i, rfl⟩) (fun i => hw r hr ⟨i, rfl⟩)
  let s1 := s0 ∪ wordWires sum
  have hsum (i : Fin (k + 1)) : (fun x => (sum x).getLsbD i.val) ∈ s1 := Or.inr ⟨i, rfl⟩
  have haw (i : Fin (k + 1)) : (fun x => (aw x).getLsbD i.val) ∈ s1 :=
    Or.inl (hw a ha ⟨i, rfl⟩)
  have hsub := synthesis_sub_linear s1 sum aw hsum haw
  have hlt := synthesis_ult s1 sum aw hsum haw
  let s2 := s1 ∪ (wordWires (fun x => sum x - aw x) ∪ {fun x => (sum x).ult (aw x)})
  let reduced := fun x => if (sum x).ult (aw x) then sum x else sum x - aw x
  have hred := synthesis_word_mux s2 sum (fun x => sum x - aw x)
    (fun x => (sum x).ult (aw x)) (Or.inr (Or.inr rfl))
    (fun i => Or.inl (hsum i)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
  let s3 := s2 ∪ wordWires reduced
  have hre := resize_wires (v := k) s3 reduced (fun _ h => Or.inr h)
    (Or.inl (Or.inl (Or.inl hz)))
  have hactive := synthesis_ult s3 b a
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (hb ⟨i, rfl⟩)))))
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (ha ⟨i, rfl⟩)))))
  have hout := synthesis_word_mux (s3 ∪ {fun x => (b x).ult (a x)})
    (fun x => (reduced x).setWidth k) b (fun x => (b x).ult (a x)) (Or.inr rfl)
    (fun i => Or.inl (hre ⟨i, rfl⟩))
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hb ⟨i, rfl⟩))))))
  exact ((Synthesis.const (s := s) false).trans
    (hadd.trans ((hsub.union hlt).trans (hred.trans (hactive.trans hout))))).mono
      Set.Subset.rfl Set.Subset.rfl (by lia)

/-- Restriction uses one shared zero gate in the native circuit convention. -/
theorem remainder_of_power (T : ℕ) (c : Circuit Boolean.signature (k + k) (k + k))
    (hc : c.Computes Boolean.interpretation (power T)) :
    ∃ out : Circuit Boolean.signature k k,
      out.Computes Boolean.interpretation (remainder T) ∧ out.size ≤ c.size + 1 := by
  let s := inputs k ∪ {fun _ : State k => false}
  let init := fun x : State k => pack (word x) (0 : BitVec k)
  have hi (i : Fin (k + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => simpa only [init, pack, Fin.append_left, word_bit] using
        (show (fun x : State k => x i) ∈ s from Or.inl ⟨i, rfl⟩)
    | right i => simp [init, pack, s]
  have h := (Synthesis.const (s := inputs k) false).trans
    (Synthesis.circuit (I := Boolean.interpretation) (s := s) c init hi)
  have hout : wires (remainder (k := k) T) ⊆
      wires (fun x => c.eval Boolean.interpretation (init x)) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Fin.natAdd k i, ?_⟩
    funext x
    change c.eval Boolean.interpretation (init x) (Fin.natAdd k i) = remainder T x i
    rw [hc (init x)]
    dsimp only [power, init]
    rw [leftWord_pack, rightWord_pack]
    rw [show (0 : BitVec k).toNat = 0 by simp]
    simp only [pack, Fin.append_right]
    by_cases hz : (word x).toNat = 0
    · simp only [advance, remainder, hz, lt_self_iff_false, and_self, ite_false, ite_true]
    · simp only [advance, remainder, hz, Nat.pos_of_ne_zero hz, and_self, ite_true, ite_false,
        Nat.zero_add]
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by lia⟩

/-- A remainder circuit gives a power circuit with linear overhead. -/
theorem power_of_remainder (T : ℕ) (c : Circuit Boolean.signature k k)
    (hc : c.Computes Boolean.interpretation (remainder T)) :
    ∃ out : Circuit Boolean.signature (k + k) (k + k),
      out.Computes Boolean.interpretation (power T) ∧ out.size ≤ c.size + 100 * (k + 1) := by
  let a := fun x : State (k + k) => leftWord x
  let b := fun x : State (k + k) => rightWord x
  let init := fun x : State (k + k) => fun i : Fin k => x (Fin.castAdd k i)
  let r := fun x => word (c.eval Boolean.interpretation (init x))
  let s := inputs (k + k) ∪ wires (fun x => c.eval Boolean.interpretation (init x))
  have ha : wordWires a ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [a, leftWord, word_bit] using
      (show (fun x : State (k + k) => x (Fin.castAdd k i)) ∈ s from Or.inl ⟨_, rfl⟩)
  have hb : wordWires b ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [b, rightWord, word_bit] using
      (show (fun x : State (k + k) => x (Fin.natAdd k i)) ∈ s from Or.inl ⟨_, rfl⟩)
  have hr : wordWires r ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [r, word_bit] using
      (show (fun x => c.eval Boolean.interpretation (init x) i) ∈ s from Or.inr ⟨i, rfl⟩)
  have hs := synthesis_addResidue s a b r ha hb hr
  have hcirc := Synthesis.circuit (I := Boolean.interpretation)
    (s := inputs (k + k)) c init (fun i => ⟨Fin.castAdd k i, rfl⟩)
  have h : Synthesis Boolean.interpretation (inputs (k + k))
      (s ∪ wordWires (fun x => addResidue (a x) (b x) (r x))) (c.size + 100 * (k + 1)) := by
    simpa only [s, wires, Set.union_assoc, Nat.zero_add] using
      (Synthesis.of_subset (I := Boolean.interpretation)
        (s := inputs (k + k)) (t := inputs (k + k)) Set.Subset.rfl).union (hcirc.comp hs)
  have hspec (x : State (k + k)) : addResidue (a x) (b x) (r x) =
      BitVec.ofNat k (advance (a x).toNat (b x).toNat T) := by
    apply addResidue_spec
    intro ha
    change (word (c.eval Boolean.interpretation (init x))).toNat = _
    rw [hc (init x), remainder_word]
    simp only [show word (init x) = a x from rfl,
      Nat.ne_of_gt ha, ite_false, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ ha).trans (a x).isLt)]
  have hout : wires (power (k := k) T) ⊆ s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)) := by
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      left
      simpa only [power, pack, Fin.append_left] using ha ⟨i, rfl⟩
    | right i =>
      right
      refine ⟨i, ?_⟩
      funext x
      simp only [hspec, power, pack, Fin.append_right, a, b]
  obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by simpa only [Nat.zero_add] using hsize⟩

end IteratedFunctions.ModulusCounter
