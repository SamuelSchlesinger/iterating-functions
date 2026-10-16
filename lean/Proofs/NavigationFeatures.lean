/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.NavigationEncoding
public import Proofs.DepthCircuit
public import Proofs.CheckpointDepth
public import Proofs.LabelCircuits

/-! # Reusable input projections and depth-word synthesis -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits
variable {n a : ℕ}

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

end IteratedFunctions
