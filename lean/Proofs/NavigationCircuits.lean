/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.NavigationSynthesis
public import Proofs.DepthCircuit
public import Proofs.LabelCircuits

/-! # Reachability and first-hitting-time circuits -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
variable {n a w v : ℕ}
noncomputable local instance navigationCircuitsStateOrder : LinearOrder (State n) := stateOrder n

/-- Zero extension and truncation only rewire available bits. -/
theorem resize_wires (s : Set (State a → Bool)) (value : State a → BitVec w)
    (hv : wordWires value ⊆ s) (hz : (fun _ => false) ∈ s) :
    wordWires (fun x => (value x).setWidth v) ⊆ s := by
  rintro _ ⟨bit, rfl⟩
  simp only [BitVec.getLsbD_setWidth, bit.isLt, decide_true, Bool.true_and]
  by_cases hi : bit.val < w
  · exact hv ⟨⟨bit.val, hi⟩, rfl⟩
  · simpa only [BitVec.getLsbD_of_ge _ _ (by lia : w ≤ bit.val)] using hz

theorem synthesis_depthWord (depth : Circuit Boolean.signature n (n + 2))
    (f : State n → State n)
    (hd : ∀ x, word (depth.eval Boolean.interpretation x) =
      BitVec.ofNat (n + 2) (transientDepth f x))
    (s : Set (State a → Bool)) (init : State a → State n)
    (hi : wires init ⊆ s) (hz : (fun _ => false) ∈ s) :
    Synthesis Boolean.interpretation s (wordWires (fun z => depthWord f (init z))) depth.size := by
  have h := Synthesis.circuit (I := Boolean.interpretation) (s := s) depth init
    (fun bit => hi ⟨bit, rfl⟩)
  let src := s ∪ wires (fun z => depth.eval Boolean.interpretation (init z))
  have hv : wordWires (fun z => word (depth.eval Boolean.interpretation (init z))) ⊆ src := by
    rintro _ ⟨bit, rfl⟩
    have he : (fun z => (word (depth.eval Boolean.interpretation (init z))).getLsbD bit.val) =
        (fun z => depth.eval Boolean.interpretation (init z) bit) := by
      funext z
      exact word_bit _ bit
    change (fun z => (word (depth.eval Boolean.interpretation (init z))).getLsbD bit.val) ∈ src
    rw [he]
    exact Or.inr ⟨bit, rfl⟩
  have hr := resize_wires (v := n + 3) src _ hv (Or.inl hz)
  have he : (fun z => (word (depth.eval Boolean.interpretation (init z))).setWidth (n + 3)) =
      (fun z => depthWord f (init z)) := by
    funext z
    rw [hd]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by lia)
      ((depth_lt_states f (init z)).trans_le (Nat.pow_le_pow_right (by decide) (by lia)))
  rw [he] at hr
  exact h.trans (Synthesis.of_subset hr)

def inputLeft (z : State (n + n)) : State n := fun i => z (Fin.castAdd n i)
def inputRight (z : State (n + n)) : State n := fun i => z (Fin.natAdd n i)

def navigationBudget (n s L : ℕ) : ℕ :=
  1 + 2 * depthBudget n s L + 20080000 * powerBudget n s (2 ^ n) L +
    (n + 3) * (40000 * powerBudget n s (2 ^ n) L + 4 * n) + 1000 * (n + 4) ^ 3

/-- The full construction uses two depths, two label records, and word arithmetic. -/
theorem navigation_circuit (c : Circuit Boolean.signature n n) (L : ℕ)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature (n + n) (1 + (n + 1)),
      out.Computes Boolean.interpretation (fun z =>
        navigationBits (c.eval Boolean.interpretation) (inputLeft z) (inputRight z)) ∧
      out.size ≤ navigationBudget n c.size L := by
  let f := c.eval Boolean.interpretation
  let x : State (n + n) → State n := inputLeft
  let y : State (n + n) → State n := inputRight
  obtain ⟨depth, hd, hds⟩ := depth_circuit c L hL hLN
  obtain ⟨labels, hl, hls⟩ := cycle_label_circuit c L hL hLN
  have hle : labels.eval Boolean.interpretation = canonicalLabel f := funext hl
  let src := inputs (n + n) ∪ {fun _ => false}
  have hx : wires x ⊆ src := by rintro _ ⟨bit, rfl⟩; exact Or.inl ⟨_, rfl⟩
  have hy : wires y ⊆ src := by rintro _ ⟨bit, rfl⟩; exact Or.inl ⟨_, rfl⟩
  have hdx := synthesis_depthWord depth f hd src x hx (Or.inr rfl)
  have hdy := synthesis_depthWord depth f hd src y hy (Or.inr rfl)
  have hlx : Synthesis Boolean.interpretation src (wires (fun z => canonicalLabel f (x z)))
      labels.size := by
    simpa only [hle, wires] using Synthesis.circuit (I := Boolean.interpretation) (s := src)
      labels x (fun bit => hx ⟨bit, rfl⟩)
  have hly : Synthesis Boolean.interpretation src (wires (fun z => canonicalLabel f (y z)))
      labels.size := by
    simpa only [hle, wires] using Synthesis.circuit (I := Boolean.interpretation) (s := src)
      labels y (fun bit => hy ⟨bit, rfl⟩)
  have hfeatures := ((hdx.union hdy).union hlx).union hly
  let all := src ∪ (wordWires (fun z => depthWord f (x z)) ∪
    wordWires (fun z => depthWord f (y z)) ∪ wires (fun z => canonicalLabel f (x z)) ∪
    wires (fun z => canonicalLabel f (y z)))
  have avx : wires (fun z => canonicalLabel f (x z)) ⊆ all :=
    fun _ h => Or.inr (Or.inl (Or.inr h))
  have avy : wires (fun z => canonicalLabel f (y z)) ⊆ all := fun _ h => Or.inr (Or.inr h)
  have decode (init : State (n + n) → State n)
      (hav : wires (fun z => canonicalLabel f (init z)) ⊆ all) :
      wires (fun z => canonicalCycle f (init z)) ⊆ all ∧
      wordWires (fun z => lengthWord f (init z)) ⊆ all ∧
      wordWires (fun z => phaseWord f (init z)) ⊆ all := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨bit, rfl⟩
      simpa only [canonicalLabel, labelBits, Fin.append_left] using
        hav ⟨Fin.castAdd ((n + 3) + (n + 3)) bit, rfl⟩
    · rintro _ ⟨bit, rfl⟩
      simpa only [canonicalLabel, labelBits, lengthWord, Fin.append_right, Fin.append_left] using
        hav ⟨Fin.natAdd n (Fin.castAdd (n + 3) bit), rfl⟩
    · rintro _ ⟨bit, rfl⟩
      simpa only [canonicalLabel, labelBits, phaseWord, Fin.append_right] using
        hav ⟨Fin.natAdd n (Fin.natAdd (n + 3) bit), rfl⟩
  have hnav := synthesis_navigation c all x y (fun _ h => Or.inl (hx h))
    (fun _ h => Or.inl (hy h))
    (fun _ h => Or.inr (Or.inl (Or.inl (Or.inl h))))
    (fun _ h => Or.inr (Or.inl (Or.inl (Or.inr h))))
    (decode x avx).2.1 (decode x avx).2.2 (decode y avy).2.2
    (decode x avx).1 (decode y avy).1 L hL hLN
  have h := (Synthesis.const (s := inputs (n + n)) false).trans
    (hfeatures.trans hnav)
  obtain ⟨out, hout, hs⟩ := h.exists_circuit_outputs
  refine ⟨out, hout, hs.trans ?_⟩
  unfold navigationBudget
  lia

/-- The extra work is at most quadratic in the state width. -/
theorem navigationBudget_le (n s L : ℕ) (hL : 0 < L) :
    navigationBudget n s L ≤ 100000000 * (n + 1) ^ 2 * powerBudget n s (2 ^ n) L := by
  have hd := depthBudget_le n s L hL
  have hb : (n + 1) ^ 3 ≤ powerBudget n s (2 ^ n) L := by
    unfold powerBudget
    have h := Nat.mul_le_mul_left ((n + 1) ^ 3)
      (show 1 ≤ L + 2 ^ n / L + 1 by lia)
    lia
  have hfour : (n + 4) ^ 3 ≤ 64 * (n + 1) ^ 3 := by
    have h := Nat.pow_le_pow_left (show n + 4 ≤ 4 * (n + 1) by lia) 3
    nlinarith
  have hpoly : 1 + (n + 3) * (4 * n) + 1000 * (n + 4) ^ 3 ≤
      65000 * powerBudget n s (2 ^ n) L := by
    nlinarith [Nat.zero_le (n ^ 3)]
  have hq : 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hlinear : n + 3 ≤ 3 * (n + 1) ^ 2 := by nlinarith
  have hB := Nat.mul_le_mul_right (powerBudget n s (2 ^ n) L) hq
  have hlinearB := Nat.mul_le_mul_right (powerBudget n s (2 ^ n) L) hlinear
  unfold navigationBudget
  nlinarith

/-- Reachability and first hitting time, with an explicit optimized gate bound. -/
theorem reachability_hitting_time (c : Circuit Boolean.signature n n) :
    ∃ out : Circuit Boolean.signature (n + n) (1 + (n + 1)),
      (∀ z, out.eval Boolean.interpretation z 0 = true ↔
        ∃ t, (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z) ∧
      (∀ z, out.eval Boolean.interpretation z 0 = true →
        let t := (word fun i : Fin (n + 1) =>
          out.eval Boolean.interpretation z (Fin.natAdd 1 i)).toNat
        (c.eval Boolean.interpretation)^[t] (inputLeft z) = inputRight z ∧
          (∀ j < t, (c.eval Boolean.interpretation)^[j] (inputLeft z) ≠ inputRight z) ∧
          t < 2 ^ n) ∧
      (out.size : ℝ) ≤ 300000000 * (n + 1 : ℝ) ^ 2 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, ho⟩ := powerBudget_optimized n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := navigation_circuit c L hL hLN
  refine ⟨out, ?_, ?_, ?_⟩
  · intro z
    rw [hout z]
    exact navigationBits_flag _ _ _
  · intro z hz
    rw [hout z] at hz ⊢
    exact navigationBits_time _ _ _ ((navigationBits_flag _ _ _).mp hz)
  · have hs' : (out.size : ℝ) ≤
        100000000 * (n + 1 : ℝ) ^ 2 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
      exact_mod_cast hs.trans (navigationBudget_le n c.size L hL)
    have h := mul_le_mul_of_nonneg_left ho (show 0 ≤ 100000000 * (n + 1 : ℝ) ^ 2 by positivity)
    nlinarith

end IteratedFunctions
