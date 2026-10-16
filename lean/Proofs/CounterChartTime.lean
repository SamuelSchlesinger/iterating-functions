/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CounterChartCircuits

/-! # Advancing sparse orbit coordinates with one streamed input-time remainder -/

@[expose] public section

namespace IteratedFunctions

attribute [local instance] counterChartBitVecFintype counterChartWordOrder

open Cslib.Circuits

variable {n m a : ℕ}

def advanceCycleLabel (r : State (n + (chartWidth n + chartWidth n)))
    (bits : Fin m → Bool) :
    State (n + (chartWidth n + chartWidth n)) :=
  labelBits (labelRepresentative r) (labelLength r)
    (ModulusCounter.addResidue (labelLength r) (labelPhase r)
      (streamRemainder (labelLength r) bits))

theorem advanceCycleLabel_spec (f : BitVec n → BitVec n) (x : BitVec n) (bits : Fin m → Bool) :
    advanceCycleLabel (wordCycleLabel f x) bits = wordCycleLabel f (f^[binaryValue bits] x) := by
  let ell := BitVec.ofNat (chartWidth n) (cycleLength f x)
  let p := BitVec.ofNat (chartWidth n) (phase f x)
  have hel : ell.toNat = cycleLength f x := chart_ofNat_toNat (cycleLength_le_words f x)
  have hp : p.toNat = phase f x := chart_ofNat_toNat
    ((phase_lt f x).le.trans (cycleLength_le_words f x))
  have hpos : 0 < ell.toNat := by rw [hel]; exact cycleLength_pos f x
  have hwide : 2 * ell.toNat ≤ 2 ^ chartWidth n := by
    rw [hel]
    have := cycleLength_le_words f x
    simp only [chartWidth, Nat.pow_succ]
    lia
  have hrem := streamRemainder_toNat ell bits hpos hwide
  have hphase : ModulusCounter.addResidue ell p (streamRemainder ell bits) =
      BitVec.ofNat (chartWidth n) (phase f (f^[binaryValue bits] x)) := by
    apply BitVec.eq_of_toNat_eq
    rw [addResidue_toNat _ _ _ (by rw [hp, hel]; exact phase_lt f x)
      (by rw [hrem]; exact Nat.mod_lt _ hpos), hrem, hp, hel]
    rw [chart_ofNat_toNat ((phase_lt f _).le.trans (cycleLength_le_words f _)),
      phase_shift, Nat.add_mod_mod]
  simp only [advanceCycleLabel, wordCycleLabel, labelRepresentative_bits,
    labelLength_bits, labelPhase_bits, canonicalCycle_iterate, cycleLength_iterate]
  exact congrArg (labelBits (fun i => (canonicalCycle f x).getLsbD i.val) ell) hphase

/-- Streaming is performed once after the input's cycle length is selected. -/
theorem synthesis_advanceCycleLabel (s : Set (State a → Bool))
    (r : State a → State (n + (chartWidth n + chartWidth n)))
    (bits : State a → Fin m → Bool) (hr : wires r ⊆ s)
    (hb : ∀ j, (fun z => bits z j) ∈ s) :
    Synthesis Boolean.interpretation s (wires fun z => advanceCycleLabel (r z) (bits z))
      (200 * (n + 3) * (m + 1)) := by
  let ell := fun z => labelLength (r z)
  let p := fun z => labelPhase (r z)
  let rem := fun z => streamRemainder (ell z) (bits z)
  have he : wordWires ell ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [ell, labelLength, word_bit] using hr ⟨_, rfl⟩
  have hp : wordWires p ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [p, labelPhase, word_bit] using hr ⟨_, rfl⟩
  have hrem := synthesis_streamRemainder s ell bits (fun i => he ⟨i, rfl⟩) hb
  let src := s ∪ wordWires rem
  have hadd := ModulusCounter.synthesis_addResidue src ell p rem
    (fun _ h => Or.inl (he h)) (fun _ h => Or.inl (hp h)) (fun _ h => Or.inr h)
  let newPhase := fun z => ModulusCounter.addResidue (ell z) (p z) (rem z)
  have hout := labelBits_wires (src ∪ wordWires newPhase)
    (fun z => labelRepresentative (r z)) ell newPhase
    (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (hr ⟨_, rfl⟩)))
    (fun _ h => Or.inl (Or.inl (he h))) (fun _ h => Or.inr h)
  exact (hrem.trans (hadd.trans (Synthesis.of_subset hout))).mono
    Set.Subset.rfl Set.Subset.rfl (by dsimp [chartWidth]; nlinarith [Nat.zero_le (n * m)])

end IteratedFunctions
