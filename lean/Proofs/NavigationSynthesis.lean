/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.NavigationEncoding
public import Proofs.BinaryNumbers

/-! # Boolean circuit assembly for navigation from depths and cycle labels -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
variable {n a : ℕ}
noncomputable local instance navigationSynthesisStateOrder : LinearOrder (State n) := stateOrder n

theorem synthesis_navigation (c : Circuit Boolean.signature n n)
    (s : Set (State a → Bool)) (x y : State a → State n)
    (hx : wires x ⊆ s) (hy : wires y ⊆ s)
    (hdx : wordWires (fun z => depthWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hdy : wordWires (fun z => depthWord (c.eval Boolean.interpretation) (y z)) ⊆ s)
    (hlx : wordWires (fun z => lengthWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hpx : wordWires (fun z => phaseWord (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hpy : wordWires (fun z => phaseWord (c.eval Boolean.interpretation) (y z)) ⊆ s)
    (hcx : wires (fun z => canonicalCycle (c.eval Boolean.interpretation) (x z)) ⊆ s)
    (hcy : wires (fun z => canonicalCycle (c.eval Boolean.interpretation) (y z)) ⊆ s)
    (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    Synthesis Boolean.interpretation s
      (wires fun z => navigationBits (c.eval Boolean.interpretation) (x z) (y z))
      ((n + 3) * (40000 * powerBudget n c.size (2 ^ n) L + 4 * n) +
        1000 * (n + 4) ^ 3) := by
  let f := c.eval Boolean.interpretation
  let dx := fun z => depthWord f (x z)
  let dy := fun z => depthWord f (y z)
  let gap := fun z => navigationGap f (x z) (y z)
  let total := fun z => phaseWord f (x z) + dx z
  let zero := fun z => decide (dy z = 0)
  let less := fun z => (dx z).ult (dy z)
  let same := fun z => decide (canonicalCycle f (x z) = canonicalCycle f (y z))
  have hg := synthesis_sub s dx dy (fun i => hdx ⟨i, rfl⟩) (fun i => hdy ⟨i, rfl⟩)
  have ht := synthesis_add s (fun z => phaseWord f (x z)) dx
    (fun i => hpx ⟨i, rfl⟩) (fun i => hdx ⟨i, rfl⟩)
  have hz := synthesis_word_eq_const s dy (fun i => hdy ⟨i, rfl⟩) 0
  have hl := synthesis_ult s dx dy (fun i => hdx ⟨i, rfl⟩) (fun i => hdy ⟨i, rfl⟩)
  have hs := synthesis_bits_eq s (fun z => canonicalCycle f (x z))
    (fun z => canonicalCycle f (y z)) hcx hcy
  have h₁ := (((hg.union ht).union hz).union hl).union hs
  let s₁ := s ∪ (wordWires gap ∪ wordWires total ∪ {zero} ∪ {less} ∪ {same})
  have old₁ : s ⊆ s₁ := fun _ h => Or.inl h
  have avGap : wordWires gap ⊆ s₁ := fun _ h =>
    Or.inr (Or.inl (Or.inl (Or.inl (Or.inl h))))
  have avTotal : wordWires total ⊆ s₁ := fun _ h =>
    Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  have avZero : zero ∈ s₁ := Or.inr (Or.inl (Or.inl (Or.inr rfl)))
  have avLess : less ∈ s₁ := Or.inr (Or.inl (Or.inr rfl))
  have avSame : same ∈ s₁ := Or.inr (Or.inr rfl)
  let dist := fun z => navigationDistance f (x z) (y z)
  let current := fun z => f^[(gap z).toNat] (x z)
  have hd := synthesis_subtractMod s₁ (fun z => phaseWord f (y z)) total
    (fun z => lengthWord f (x z)) (fun i => old₁ (hpy ⟨i, rfl⟩))
    (fun i => avTotal ⟨i, rfl⟩) (fun i => old₁ (hlx ⟨i, rfl⟩))
  have hi := synthesis_variable_time c s₁ x (fun z i => (gap z).getLsbD i.val)
    (fun _ h => old₁ (hx h)) (fun i => avGap ⟨i, rfl⟩) L hL hLN
  simp only [binaryValue_bits] at hi
  have h₂ := hd.union hi
  let s₂ := s₁ ∪ (wordWires dist ∪ wires current)
  have old₂ : s₁ ⊆ s₂ := fun _ h => Or.inl h
  have avDist : wordWires dist ⊆ s₂ := fun _ h => Or.inr (Or.inl h)
  have avCurrent : wires current ⊆ s₂ := fun _ h => Or.inr (Or.inr h)
  let cyclicTime := fun z => dx z + dist z
  let equal := fun z => decide (current z = y z)
  have ha := synthesis_add s₂ dx dist
    (fun i => old₂ (old₁ (hdx ⟨i, rfl⟩))) (fun i => avDist ⟨i, rfl⟩)
  have he := synthesis_bits_eq s₂ current y avCurrent (fun _ h => old₂ (old₁ (hy h)))
  have h₃ := ha.union he
  let s₃ := s₂ ∪ (wordWires cyclicTime ∪ {equal})
  have old₃ : s₂ ⊆ s₃ := fun _ h => Or.inl h
  have avCyclicTime : wordWires cyclicTime ⊆ s₃ := fun _ h => Or.inr (Or.inl h)
  have avEqual : equal ∈ s₃ := Or.inr (Or.inr rfl)
  have hb := (Synthesis.of_mem (I := Boolean.interpretation)
    (old₃ (old₂ avLess))).not.and (Synthesis.of_mem avEqual)
  have hf := hb.trans (Synthesis.mux (s := s₃ ∪ {fun z => !less z && equal z})
    (Or.inl (old₃ (old₂ avZero))) (Or.inl (old₃ (old₂ avSame))) (Or.inr rfl))
  have hm := synthesis_word_mux s₃ cyclicTime gap zero (old₃ (old₂ avZero))
    (fun i => avCyclicTime ⟨i, rfl⟩) (fun i => old₃ (old₂ (avGap ⟨i, rfl⟩)))
  have h₄ : Synthesis Boolean.interpretation s₃
      ({fun z => navigationFlag f (x z) (y z)} ∪
        wordWires (fun z => navigationTime f (x z) (y z))) (6 + 4 * (n + 3)) := by
    have hflag : (fun z => if zero z then same z else !less z && equal z) =
        (fun z => navigationFlag f (x z) (y z)) := by
      funext z
      apply Bool.eq_iff_iff.mpr
      simp only [zero, same, less, equal, current, gap, dx, dy, navigationFlag,
        decide_eq_true_eq]
    have htime : (fun z => if zero z then cyclicTime z else gap z) =
        (fun z => navigationTime f (x z) (y z)) := by
      funext z
      simp only [zero, cyclicTime, gap, dx, dy, dist, decide_eq_true_eq, navigationTime]
    rw [hflag] at hf
    change Synthesis _ s₃ (wordWires (fun z => if zero z then cyclicTime z else gap z)) _ at hm
    rw [htime] at hm
    exact hf.union hm
  have h₅ := Synthesis.of_subset (I := Boolean.interpretation) (s := s₃ ∪
      ({fun z => navigationFlag f (x z) (y z)} ∪
        wordWires (fun z => navigationTime f (x z) (y z))))
      (t := wires (fun z => navigationBits f (x z) (y z))) (by
    rintro _ ⟨bit, rfl⟩
    induction bit using Fin.addCases with
    | left bit =>
      apply Or.inr ∘ Or.inl
      simp only [Set.mem_singleton_iff, navigationBits, Fin.append_left]
    | right bit =>
      apply Or.inr ∘ Or.inr
      refine ⟨⟨bit.val, by have := bit.isLt; lia⟩, ?_⟩
      simp only [navigationBits, Fin.append_right])
  exact (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))).mono
    Set.Subset.rfl Set.Subset.rfl (by nlinarith [Nat.zero_le (n ^ 3)])

end IteratedFunctions
