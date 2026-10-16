/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CycleProjection
public import Proofs.LabelCircuits
public import Proofs.NavigationEncoding
public import Proofs.StreamingRemainder

/-!
# Arbitrarily wide input times with additive arithmetic cost

Cycle length reduces a long time to fewer than twice the number of states.
Only the remainder computation reads all input time bits. The expensive binary
powering circuit then uses only `n + 3` bits.
-/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n m a : ℕ}
noncomputable local instance longTimeStateOrder : LinearOrder (State n) := stateOrder n

noncomputable def compressedTimeWord (f : State n → State n) (x : State n)
    (bits : Fin m → Bool) : BitVec (n + 3) :=
  if (word bits).ult (BitVec.ofNat m (2 ^ n)) then (word bits).setWidth (n + 3)
  else BitVec.ofNat (n + 3) (2 ^ n) +
    subtractMod (streamRemainder (lengthWord f x) bits)
      (BitVec.ofNat (n + 3) (2 ^ n)) (lengthWord f x)

theorem compressedTimeWord_toNat (f : State n → State n) (x : State n)
    (bits : Fin m → Bool) (hnm : n < m) :
    (compressedTimeWord f x bits).toNat = normalizedTime f x (binaryValue bits) := by
  have hN : 2 ^ n < 2 ^ (n + 3) := Nat.pow_lt_pow_right (by decide) (by lia)
  have hNm : 2 ^ n < 2 ^ m := Nat.pow_lt_pow_right (by decide) hnm
  have hl := cycleLength_le_states f x
  have hp := cycleLength_pos f x
  have hr := streamRemainder_toNat (lengthWord f x) bits
    (by simpa using hp) (by simp only [lengthWord_toNat, Nat.pow_succ]; lia)
  simp only [lengthWord_toNat] at hr
  have hlt := Nat.mod_lt (binaryValue bits) hp
  unfold compressedTimeWord normalizedTime
  simp only [BitVec.ult, word_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNm,
    decide_eq_true_eq, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  split_ifs with ht
  · rw [BitVec.toNat_setWidth, word_toNat, Nat.mod_eq_of_lt (ht.trans hN)]
  · have hd : (subtractMod (streamRemainder (lengthWord f x) bits)
          (BitVec.ofNat (n + 3) (2 ^ n)) (lengthWord f x)).toNat =
        (binaryValue bits - 2 ^ n) % cycleLength f x := by
      rw [subtractMod_spec]
      · simp only [hr, lengthWord_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
        apply subtractModNat_eq hp (Nat.mod_lt _ hp)
        change (((binaryValue bits - 2 ^ n) % cycleLength f x) + 2 ^ n) %
          cycleLength f x = (binaryValue bits % cycleLength f x) % cycleLength f x
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.sub_add_cancel (by lia), Nat.mod_mod]
      · simpa using hp
      · simp only [hr, lengthWord_toNat, Nat.pow_succ]
        lia
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, hd]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt (binaryValue bits - 2 ^ n) hp
    simp only [Nat.pow_succ]
    lia

theorem synthesis_compressedTime (s : Set (State a → Bool))
    (f : State n → State n) (init : State a → State n) (bits : State a → Fin m → Bool)
    (hl : wordWires (fun z => lengthWord f (init z)) ⊆ s)
    (hb : ∀ j, (fun z => bits z j) ∈ s)
    (hc : ∀ b : Bool, (fun _ : State a => b) ∈ s) :
    Synthesis Boolean.interpretation s
      (wordWires fun z => compressedTimeWord f (init z) (bits z))
      (4 + m * (51 * (n + 3) + 9) + 300 * (n + 4) ^ 3 + 24 * (n + 3)) := by
  let ell := fun z => lengthWord f (init z)
  let rem := fun z => streamRemainder (ell z) (bits z)
  let bound := fun _ : State a => BitVec.ofNat (n + 3) (2 ^ n)
  have hrem := synthesis_streamRemainder s ell bits (fun i => hl ⟨i, rfl⟩) hb
  let s1 := s ∪ wordWires rem
  let difference := fun z => subtractMod (rem z) (bound z) (ell z)
  have hdiff := synthesis_subtractMod s1 rem bound ell
    (fun i => Or.inr ⟨i, rfl⟩)
    (fun i => Or.inl (hc ((BitVec.ofNat (n + 3) (2 ^ n)).getLsbD i.val)))
    (fun i => Or.inl (hl ⟨i, rfl⟩))
  let s2 := s1 ∪ wordWires difference
  let advance := fun z => bound z + difference z
  have hadd := synthesis_add_linear s2 bound difference
    (fun i => Or.inl (Or.inl (hc ((BitVec.ofNat (n + 3) (2 ^ n)).getLsbD i.val))))
    (fun i => Or.inr ⟨i, rfl⟩)
  let s3 := s2 ∪ wordWires advance
  let short := fun z => (word (bits z)).ult (BitVec.ofNat m (2 ^ n))
  have hcmp := synthesis_ult s3 (fun z => word (bits z))
    (fun _ => BitVec.ofNat m (2 ^ n))
    (fun i => by
      simp only [word_bit]
      exact Or.inl (Or.inl (Or.inl (hb i))))
    (fun i => Or.inl (Or.inl (Or.inl (hc ((BitVec.ofNat m (2 ^ n)).getLsbD i.val)))))
  let s4 := s3 ∪ {short}
  have hword : wordWires (fun z => word (bits z)) ⊆ s4 := by
    rintro _ ⟨i, rfl⟩
    simp only [word_bit]
    exact Or.inl (Or.inl (Or.inl (Or.inl (hb i))))
  have hresize := resize_wires (v := n + 3) s4 (fun z => word (bits z)) hword
    (Or.inl (Or.inl (Or.inl (Or.inl (hc false)))))
  have hmux := synthesis_word_mux s4 (fun z => (word (bits z)).setWidth (n + 3))
    advance short (Or.inr rfl) (fun i => hresize ⟨i, rfl⟩)
    (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
  exact (hrem.trans (hdiff.trans (hadd.trans (hcmp.trans hmux)))).mono
    Set.Subset.rfl Set.Subset.rfl (by lia)

def longTimeBudget (n s m L : ℕ) : ℕ :=
  6 + 10040000 * powerBudget n s (2 ^ n) L +
    m * (51 * (n + 3) + 9) + 300 * (n + 4) ^ 3 + 24 * (n + 3) +
    (n + 3) * (40000 * powerBudget n s (2 ^ n) L + 4 * n)

theorem long_time_circuit (c : Circuit Boolean.signature n n) (m L : ℕ)
    (hnm : n < m) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ z, out.eval Boolean.interpretation z =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => z (Fin.natAdd n j))]
          (fun i => z (Fin.castAdd m i))) ∧
      out.size ≤ longTimeBudget n c.size m L := by
  let f := c.eval Boolean.interpretation
  let init := fun z : State (n + m) => fun i : Fin n => z (Fin.castAdd m i)
  let bits := fun z : State (n + m) => fun j : Fin m => z (Fin.natAdd n j)
  let constants : Set (State (n + m) → Bool) := {fun _ => false, fun _ => true}
  let src := inputs (n + m) ∪ constants
  have hc (b : Bool) : (fun _ : State (n + m) => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis Boolean.interpretation (inputs (n + m)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  have heval : labels.eval Boolean.interpretation = canonicalLabel f := funext hl
  have hlabels : Synthesis Boolean.interpretation src
      (wires (fun z => canonicalLabel f (init z))) labels.size := by
    simpa only [heval, wires] using Synthesis.circuit (I := Boolean.interpretation)
      (s := src) labels init (fun i => Or.inl ⟨_, rfl⟩)
  let s1 := src ∪ wires (fun z => canonicalLabel f (init z))
  have hlength : wordWires (fun z => lengthWord f (init z)) ⊆ s1 := by
    rintro _ ⟨bit, rfl⟩
    have h : (fun z => canonicalLabel f (init z)
        (Fin.natAdd n (Fin.castAdd (n + 3) bit))) ∈ s1 := Or.inr ⟨_, rfl⟩
    simpa only [canonicalLabel, labelBits, lengthWord, Fin.append_right, Fin.append_left]
      using h
  have htime := synthesis_compressedTime s1 f init bits hlength
    (fun j => Or.inl (Or.inl ⟨_, rfl⟩)) (fun b => Or.inl (hc b))
  let time := fun z => compressedTimeWord f (init z) (bits z)
  let s2 := s1 ∪ wordWires time
  have hpower := synthesis_variable_time c s2 init
    (fun z (i : Fin (n + 3)) => (time z).getLsbD i.val)
    (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))
    (fun i => Or.inr ⟨i, rfl⟩) L hL hLN
  obtain ⟨out, ho, hs⟩ :=
    (hconst.trans (hlabels.trans (htime.trans hpower))).exists_circuit_outputs
  refine ⟨out, fun z => ?_, ?_⟩
  · rw [ho z]
    change f^[binaryValue (fun i : Fin (n + 3) => (time z).getLsbD i.val)] (init z) =
      f^[binaryValue (bits z)] (init z)
    rw [binaryValue_bits, compressedTimeWord_toNat f _ _ hnm]
    exact iterate_normalizedTime f (init z) (binaryValue (bits z))
  · unfold longTimeBudget
    lia

theorem longTimeBudget_le (n s m L : ℕ) :
    longTimeBudget n s m L ≤
      11000000 * (n + 1) * powerBudget n s (2 ^ n) L + 200 * m * (n + 1) := by
  have hb : (n + 1) ^ 3 ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    have h := Nat.mul_le_mul_left ((n + 1) ^ 3)
      (show 1 ≤ L + 2 ^ n / L + 1 by lia)
    lia
  have hfour : (n + 4) ^ 3 ≤ 64 * (n + 1) ^ 3 := by
    have h := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by lia) 3
    nlinarith
  have hpoly : 6 + 300 * (n + 4) ^ 3 + 24 * (n + 3) + (n + 3) * (4 * n) ≤
      20000 * powerBudget n s (2 ^ n) L := by
    nlinarith [Nat.zero_le (n ^ 3)]
  have htime := Nat.mul_le_mul_left m (show 51 * (n + 3) + 9 ≤ 200 * (n + 1) by lia)
  have hcost := Nat.mul_le_mul_right (powerBudget n s (2 ^ n) L)
    (show 10040000 + (n + 3) * 40000 + 20000 ≤ 11000000 * (n + 1) by lia)
  unfold longTimeBudget
  nlinarith

/-- Processing additional time bits adds `O(n)` gates per bit, independently of `B`. -/
theorem variable_time_additive (c : Circuit Boolean.signature n n) (m L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ z, out.eval Boolean.interpretation z =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => z (Fin.natAdd n j))]
          (fun i => z (Fin.castAdd m i))) ∧
      out.size ≤ 11000000 * (n + 1) * powerBudget n c.size (2 ^ n) L +
        200 * m * (n + 1) := by
  by_cases hnm : n < m
  · obtain ⟨out, ho, hs⟩ := long_time_circuit c m L hnm hL hLN
    exact ⟨out, ho, hs.trans (longTimeBudget_le n c.size m L)⟩
  · obtain ⟨out, ho, hs⟩ := variable_time c m L hL hLN
    refine ⟨out, ho, hs.trans ?_⟩
    have hb := Nat.mul_le_mul_right (powerBudget n c.size (2 ^ n) L)
      (show m * 40000 ≤ 11000000 * (n + 1) by lia)
    nlinarith

theorem variable_time_additive_optimized (c : Circuit Boolean.signature n n) (m : ℕ) :
    ∃ out : Circuit Boolean.signature (n + m) n,
      (∀ z, out.eval Boolean.interpretation z =
        (c.eval Boolean.interpretation)^[binaryValue (fun j => z (Fin.natAdd n j))]
          (fun i => z (Fin.castAdd m i))) ∧
      (out.size : ℝ) ≤ 33000000 * (n + 1) * optimizedBudget n c.size (2 ^ n) +
        200 * m * (n + 1) := by
  obtain ⟨L, hL, hLN, hopt⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, ho, hs⟩ := variable_time_additive c m L hL hLN
  refine ⟨out, ho, ?_⟩
  have hs' : (out.size : ℝ) ≤
      11000000 * (n + 1) * (powerBudget n c.size (2 ^ n) L : ℝ) +
        200 * m * (n + 1) := by exact_mod_cast hs
  have h := mul_le_mul_of_nonneg_left hopt (show 0 ≤ 11000000 * (n + 1 : ℝ) by positivity)
  nlinarith

end IteratedFunctions
