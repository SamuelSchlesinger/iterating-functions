/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Navigation
public import Proofs.LabelEncoding

/-! # Bounded-word navigation formulas -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
variable {n : ℕ}
noncomputable local instance navigationEncodingStateOrder : LinearOrder (State n) := stateOrder n

noncomputable def depthWord (f : State n → State n) (x : State n) : BitVec (n + 3) :=
  BitVec.ofNat (n + 3) (transientDepth f x)

noncomputable def phaseWord (f : State n → State n) (x : State n) : BitVec (n + 3) :=
  BitVec.ofNat (n + 3) (phase f x)

noncomputable def lengthWord (f : State n → State n) (x : State n) : BitVec (n + 3) :=
  BitVec.ofNat (n + 3) (cycleLength f x)

theorem depth_lt_states (f : State n → State n) (x : State n) :
    transientDepth f x < 2 ^ n := by simpa using transientDepth_lt_card f x

@[simp] theorem depthWord_toNat (f : State n → State n) (x : State n) :
    (depthWord f x).toNat = transientDepth f x := by
  apply Nat.mod_eq_of_lt
  exact (depth_lt_states f x).trans_le (Nat.pow_le_pow_right (by decide) (by lia))

@[simp] theorem phaseWord_toNat (f : State n → State n) (x : State n) :
    (phaseWord f x).toNat = phase f x := Nat.mod_eq_of_lt (label_number_bounds f x).2.1

@[simp] theorem lengthWord_toNat (f : State n → State n) (x : State n) :
    (lengthWord f x).toNat = cycleLength f x := Nat.mod_eq_of_lt (label_number_bounds f x).1

@[simp] theorem depthWord_eq_zero (f : State n → State n) (x : State n) :
    depthWord f x = 0 ↔ transientDepth f x = 0 := by
  rw [← BitVec.toNat_inj, depthWord_toNat]
  rfl

noncomputable def navigationGap (f : State n → State n) (x y : State n) : BitVec (n + 3) :=
  depthWord f x - depthWord f y

noncomputable def navigationDistance (f : State n → State n) (x y : State n) : BitVec (n + 3) :=
  subtractMod (phaseWord f y) (phaseWord f x + depthWord f x) (lengthWord f x)

noncomputable def navigationFlag (f : State n → State n) (x y : State n) : Bool :=
  if depthWord f y = 0 then decide (canonicalCycle f x = canonicalCycle f y)
  else !(depthWord f x).ult (depthWord f y) &&
    decide (f^[(navigationGap f x y).toNat] x = y)

noncomputable def navigationTime (f : State n → State n) (x y : State n) : BitVec (n + 3) :=
  if depthWord f y = 0 then depthWord f x + navigationDistance f x y
  else navigationGap f x y

theorem navigationGap_spec (f : State n → State n) (x y : State n)
    (hle : transientDepth f y ≤ transientDepth f x) :
    (navigationGap f x y).toNat = transientDepth f x - transientDepth f y := by
  unfold navigationGap
  have hb : depthWord f y ≤ depthWord f x := by
    change (depthWord f y).toNat ≤ (depthWord f x).toNat
    simpa using hle
  rw [BitVec.toNat_sub_of_le hb, depthWord_toNat, depthWord_toNat]

theorem navigationDistance_spec (f : State n → State n) (x y : State n) :
    (navigationDistance f x y).toNat = cyclicDistance f x y := by
  have hμ := depth_lt_states f x
  have hpx := (phase_lt f x).trans_le (cycleLength_le_states f x)
  have hpy := (phase_lt f y).trans_le (cycleLength_le_states f y)
  have hl := cycleLength_le_states f x
  have hsum : phase f x + transientDepth f x < 2 ^ (n + 3) := by
    simp only [Nat.pow_succ]; lia
  have hsum' : phase f y + cycleLength f x < 2 ^ (n + 3) := by
    simp only [Nat.pow_succ]; lia
  unfold navigationDistance
  rw [subtractMod_spec]
  · simp only [phaseWord_toNat, depthWord_toNat, lengthWord_toNat,
      BitVec.toNat_add, Nat.mod_eq_of_lt hsum, subtractModNat, cyclicDistance]
  · simpa using cycleLength_pos f x
  · simpa using hsum'

theorem navigationFlag_spec (f : State n → State n) (x y : State n) :
    navigationFlag f x y = reaches f x y := by
  unfold navigationFlag reaches
  simp only [depthWord_eq_zero]
  split_ifs with hy
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
  · by_cases hle : transientDepth f y ≤ transientDepth f x
    · simp only [BitVec.ult_eq_decide, depthWord_toNat,
        show ¬ transientDepth f x < transientDepth f y by lia, decide_false, Bool.not_false,
        Bool.true_and, hle, decide_true, navigationGap_spec f x y hle]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
    · simp only [BitVec.ult_eq_decide, depthWord_toNat,
        show transientDepth f x < transientDepth f y by lia, decide_true, Bool.not_true,
        Bool.false_and, hle, decide_false]

theorem navigationTime_spec (f : State n → State n) (x y : State n)
    (h : reaches f x y = true) :
    (navigationTime f x y).toNat = hittingTime f x y := by
  unfold navigationTime hittingTime
  simp only [depthWord_eq_zero]
  split_ifs with hy
  · rw [BitVec.toNat_add, depthWord_toNat, navigationDistance_spec]
    apply Nat.mod_eq_of_lt
    have hd : cyclicDistance f x y < cycleLength f x :=
      Nat.mod_lt _ (cycleLength_pos f x)
    have hμ := depth_lt_states f x
    have hl := cycleLength_le_states f x
    simp only [Nat.pow_succ]
    lia
  · apply navigationGap_spec
    exact ((transient_reachable_iff f x y (fun hp =>
      hy ((transientDepth_eq_zero_iff f y).mpr hp))).mp ((reaches_iff f x y).mp h)).1

/-- One reachability bit followed by an `(n+1)`-bit first hitting time. -/
noncomputable def navigationBits (f : State n → State n) (x y : State n) : State (1 + (n + 1)) :=
  Fin.append (fun _ => navigationFlag f x y)
    (fun i => (navigationTime f x y).getLsbD i.val)

theorem navigationBits_flag (f : State n → State n) (x y : State n) :
    navigationBits f x y 0 = true ↔ ∃ t, f^[t] x = y := by
  change navigationFlag f x y = true ↔ _
  rw [navigationFlag_spec, reaches_iff]

theorem navigationBits_time (f : State n → State n) (x y : State n)
    (h : ∃ t, f^[t] x = y) :
    let t := (word fun i : Fin (n + 1) => navigationBits f x y (Fin.natAdd 1 i)).toNat
    f^[t] x = y ∧ (∀ j < t, f^[j] x ≠ y) ∧ t < 2 ^ n := by
  have hr := (reaches_iff f x y).mpr h
  have ht := hittingTime_spec f x y hr
  have hb : hittingTime f x y < 2 ^ n := by simpa using ht.2.2
  have he : (word fun i : Fin (n + 1) => navigationBits f x y (Fin.natAdd 1 i)) =
      (navigationTime f x y).setWidth (n + 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [word_bit _ ⟨i, hi⟩]
    simp only [navigationBits, Fin.append_right, BitVec.getLsbD_setWidth, hi,
      decide_true, Bool.true_and]
  dsimp only
  rw [he, BitVec.toNat_setWidth, navigationTime_spec f x y hr,
    Nat.mod_eq_of_lt (hb.trans_le (Nat.pow_le_pow_right (by decide) (by lia)))]
  exact ⟨ht.1, ht.2.1, hb⟩

end IteratedFunctions
