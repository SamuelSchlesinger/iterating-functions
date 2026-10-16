/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ShortCycle
public import Proofs.PhaseArithmetic

/-! # Bit encodings of exact cycle labels and checkpoint phase corrections -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
variable {n a w : ℕ}
noncomputable local instance labelEncodingStateOrder : LinearOrder (State n) := stateOrder n

def labelBits (c : State n) (ell phi : BitVec w) : State (n + (w + w)) :=
  Fin.append c (Fin.append (fun i => ell.getLsbD i.val) (fun i => phi.getLsbD i.val))

def labelRepresentative (r : State (n + (w + w))) : State n :=
  fun i => r (Fin.castAdd (w + w) i)

def labelLength (r : State (n + (w + w))) : BitVec w :=
  word fun i => r (Fin.natAdd n (Fin.castAdd w i))

def labelPhase (r : State (n + (w + w))) : BitVec w :=
  word fun i => r (Fin.natAdd n (Fin.natAdd w i))

@[simp] theorem labelRepresentative_bits (c : State n) (ell phi : BitVec w) :
    labelRepresentative (labelBits c ell phi) = c := by
  funext i
  simp only [labelRepresentative, labelBits, Fin.append_left]
@[simp] theorem labelLength_bits (c : State n) (ell phi : BitVec w) :
    labelLength (labelBits c ell phi) = ell := by
  simp only [labelLength, labelBits, Fin.append_left, Fin.append_right, word_bits]
@[simp] theorem labelPhase_bits (c : State n) (ell phi : BitVec w) :
    labelPhase (labelBits c ell phi) = phi := by
  simp only [labelPhase, labelBits, Fin.append_right, word_bits]

noncomputable def canonicalLabel (f : State n → State n) (x : State n) :
    State (n + ((n + 3) + (n + 3))) :=
  labelBits (canonicalCycle f x) (BitVec.ofNat (n + 3) (cycleLength f x))
    (BitVec.ofNat (n + 3) (phase f x))

theorem cycleLength_le_states (f : State n → State n) (x : State n) :
    cycleLength f x ≤ 2 ^ n := by
  have h := depth_add_cycleLength_le_card f x
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
  lia

theorem label_number_bounds (f : State n → State n) (x : State n) :
    cycleLength f x < 2 ^ (n + 3) ∧ phase f x < 2 ^ (n + 3) ∧
      phase f x + cycleLength f x < 2 ^ (n + 3) := by
  have hl := cycleLength_le_states f x
  have hp := phase_lt f x
  simp only [Nat.pow_succ]
  lia

def correctLabel (r : State (n + (w + w))) (j : ℕ) : State (n + (w + w)) :=
  labelBits (labelRepresentative r) (labelLength r)
    (subtractMod (labelPhase r) (BitVec.ofNat w j) (labelLength r))

theorem correctLabel_spec (f : State n → State n) (x : State n) (j : ℕ)
    (hj : j < 2 ^ (n + 3)) :
    correctLabel (canonicalLabel f (f^[j] x)) j = canonicalLabel f x := by
  have hb := label_number_bounds f (f^[j] x)
  simp only [correctLabel, canonicalLabel, labelRepresentative_bits,
    labelLength_bits, labelPhase_bits, canonicalCycle_iterate, cycleLength_iterate]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hl := (label_number_bounds f x).1
  have hp := (label_number_bounds f (f^[j] x)).2.1
  rw [subtractMod_spec]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (label_number_bounds f x).2.1]
    apply subtractModNat_eq (cycleLength_pos f x) (phase_lt f x)
    change (phase f x + j) % cycleLength f x = phase f (f^[j] x) % cycleLength f x
    rw [phase_shift, Nat.mod_mod]
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl] using cycleLength_pos f x
  · simpa only [BitVec.toNat_ofNat, cycleLength_iterate,
      Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hl] using hb.2.2

noncomputable def shortLabel (f : State n → State n) (K : ℕ) (x : State n) :
    State (n + ((n + 3) + (n + 3))) :=
  labelBits (shortRepresentative f K x) (shortLength f K x)
    (subtractMod 0 (shortTime f K x) (shortLength f K x))

theorem shortLabel_spec (f : State n → State n) (K : ℕ) (x : State n)
    (hx : x ∈ Function.periodicPts f) (hK : cycleLength f x ≤ K) :
    shortLabel f K x = canonicalLabel f x := by
  simp only [shortLabel, canonicalLabel, shortRepresentative_spec f K x hx hK,
    shortLength_spec f K x hx hK, shortTime_spec f K x hx hK]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hl := (label_number_bounds f x).1
  have ht := (canonicalTime_lt_cycleLength f x hx).trans hl
  have hz : (0 : BitVec (n + 3)).toNat = 0 := by simp
  rw [subtractMod_spec]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hl, hz,
      subtractModNat, Nat.zero_add]
    exact (Nat.mod_eq_of_lt (phase_lt f x |>.trans hl)).symm
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl] using cycleLength_pos f x
  · simpa only [hz, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hl] using hl

theorem labelBits_wires (s : Set (State a → Bool)) (c : State a → State n)
    (ell phi : State a → BitVec w)
    (hc : wires c ⊆ s) (he : wordWires ell ⊆ s) (hp : wordWires phi ⊆ s) :
    wires (fun x => labelBits (c x) (ell x) (phi x)) ⊆ s := by
  rintro _ ⟨bit, rfl⟩
  induction bit using Fin.addCases with
  | left bit => simpa only [labelBits, Fin.append_left] using hc ⟨bit, rfl⟩
  | right bit =>
    induction bit using Fin.addCases with
    | left bit => simpa only [labelBits, Fin.append_right, Fin.append_left] using he ⟨bit, rfl⟩
    | right bit => simpa only [labelBits, Fin.append_right] using hp ⟨bit, rfl⟩

theorem synthesis_correctLabel (s : Set (State a → Bool))
    (r : State a → State (n + (w + w))) (hr : wires r ⊆ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) (j : ℕ) :
    Synthesis Boolean.interpretation s (wires fun x => correctLabel (r x) j)
      (300 * (w + 1) ^ 3) := by
  have hp := synthesis_subtractMod s (fun x => labelPhase (r x))
    (fun _ => BitVec.ofNat w j) (fun x => labelLength (r x))
    (fun i => by simpa only [labelPhase, word_bit] using hr ⟨_, rfl⟩)
    (fun i => hc _) (fun i => by simpa only [labelLength, word_bit] using hr ⟨_, rfl⟩)
  have h := hp.trans (Synthesis.of_subset (labelBits_wires _
    (fun x => labelRepresentative (r x)) (fun x => labelLength (r x))
    (fun x => subtractMod (labelPhase (r x)) (BitVec.ofNat w j) (labelLength (r x)))
    (by rintro _ ⟨bit, rfl⟩; exact Or.inl (hr ⟨_, rfl⟩))
    (by
      rintro _ ⟨bit, rfl⟩
      apply Or.inl
      simpa only [labelLength, word_bit] using hr ⟨_, rfl⟩)
    (fun _ h => Or.inr h)))
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by lia)

theorem synthesis_shortLabel (s : Set (State a → Bool)) (f : State n → State n)
    (init : State a → State n) (K : ℕ)
    (hp : ∀ j : Fin (K + 1), ∀ bit, (fun x => f^[j.val] (init x) bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) :
    Synthesis Boolean.interpretation s (wires fun x => shortLabel f K (init x))
      ((K + 1) * (30 * (n + (n + 3) + 1)) + 300 * (n + 4) ^ 3) := by
  let rep := fun x => shortRepresentative f K (init x)
  let ell := fun x => shortLength (w := n + 3) f K (init x)
  let time := fun x => shortTime (w := n + 3) f K (init x)
  have hshort := synthesis_short_labels (w := n + 3) s f init K hp hc
  let src := s ∪ (wires rep ∪ wordWires ell ∪ wordWires time)
  have hphase := synthesis_subtractMod src (fun _ => (0 : BitVec (n + 3))) time ell
    (fun _ => Or.inl (hc _)) (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
    (fun i => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩)))
  have hout := Synthesis.of_subset (I := Boolean.interpretation)
    (labelBits_wires (src ∪ wordWires (fun x => subtractMod 0 (time x) (ell x))) rep ell _
      (fun _ h => Or.inl (Or.inr (Or.inl (Or.inl h))))
      (fun _ h => Or.inl (Or.inr (Or.inl (Or.inr h)))) (fun _ h => Or.inr h))
  exact (hshort.trans (hphase.trans hout)).mono Set.Subset.rfl Set.Subset.rfl (by lia)

end IteratedFunctions
