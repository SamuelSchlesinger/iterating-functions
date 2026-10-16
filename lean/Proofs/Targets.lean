/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Applications
public import Proofs.FiniteOrbit
public import Proofs.Optimization

/-! # Recognizable target sets and terminating complete configurations -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

variable {n : ℕ}

theorem absorbing_circuit (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) :
    ∃ g : Circuit Boolean.signature n n,
      g.Computes Boolean.interpretation
        (absorb (c.eval Boolean.interpretation)
          (fun x => p.eval Boolean.interpretation x 0 = true)) ∧
      g.size ≤ c.size + p.size + 4 * n := by
  have hc := Synthesis.circuit (I := Boolean.interpretation) (s := inputs n) c id
    (fun i => ⟨i, rfl⟩)
  have hp := Synthesis.circuit (I := Boolean.interpretation) (s := inputs n) p id
    (fun i => ⟨i, rfl⟩)
  have hp' : Synthesis Boolean.interpretation (inputs n)
      {fun x => p.eval Boolean.interpretation x 0} p.size :=
    hp.mono Set.Subset.rfl (by rintro _ rfl; exact ⟨0, rfl⟩) le_rfl
  have hi : Synthesis Boolean.interpretation (inputs n) (wires (id : State n → State n)) 0 :=
    Synthesis.of_subset Set.Subset.rfl
  obtain ⟨g, hg, hs⟩ := (synthesis_ite hi hc hp').exists_circuit_outputs
  exact ⟨g, hg, by simpa using hs⟩

/-- The output state is the first target on positive instances; the predicate recognizes success. -/
theorem first_target_state (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      (∀ x, p.eval Boolean.interpretation (out.eval Boolean.interpretation x) 0 = true ↔
        ∃ t, p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      (∀ x, (∃ t, p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) →
        ∃ t < 2 ^ n,
          out.eval Boolean.interpretation x = (c.eval Boolean.interpretation)^[t] x ∧
          p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true ∧
          ∀ j < t, p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[j] x) 0 ≠ true) ∧
      out.size ≤ 40000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L := by
  let f := c.eval Boolean.interpretation
  let P := fun x => p.eval Boolean.interpretation x 0 = true
  obtain ⟨g, hg, hgs⟩ := absorbing_circuit c p
  obtain ⟨out, hout, hs⟩ := fixed_power n g (2 ^ n) L hL hLN
  have he : g.eval Boolean.interpretation = absorb f P := funext hg
  have hcard : Fintype.card (State n) = 2 ^ n := by simp
  have ho (x) : out.eval Boolean.interpretation x = (absorb f P)^[Fintype.card (State n)] x := by
    rw [hout x, he, hcard]
  refine ⟨out, fun x => ?_, fun x hx => ?_, hs.trans ?_⟩
  · rw [ho x]
    exact absorb_eventual_iff f P x
  · obtain ⟨t, ht, hp, hfirst, heq⟩ := absorb_first_visit f P x hx
    exact ⟨t, by simpa [hcard] using ht, (ho x).trans heq, hp, hfirst⟩
  · unfold powerBudget
    gcongr

/-- Eventual membership in a fixed efficiently recognizable target set. -/
theorem target_reachability (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n 1,
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        ∃ t, p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      out.size ≤ 40000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size := by
  obtain ⟨state, hp, _, hs⟩ := first_target_state c p L hL hLN
  refine ⟨p.comp state, ?_, ?_⟩
  · simpa only [Circuit.eval_comp] using hp
  · simpa only [Circuit.size_comp, Nat.add_comm] using Nat.add_le_add_right hs p.size

/-- All persistent information is included in the `n` state bits. No recognizer cost is required
when absorption and termination are supplied as semantic hypotheses. -/
theorem halting_computation (c : Circuit Boolean.signature n n) (H : State n → Prop)
    (initial : Set (State n)) (hstop : ∀ x, H x → c.eval Boolean.interpretation x = x)
    (hhalt : ∀ x ∈ initial, ∃ t, H ((c.eval Boolean.interpretation)^[t] x))
    (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n n,
      (∀ x ∈ initial, H (out.eval Boolean.interpretation x) ∧
        ∃ t < 2 ^ n, out.eval Boolean.interpretation x = (c.eval Boolean.interpretation)^[t] x ∧
          ∀ j < t, ¬ H ((c.eval Boolean.interpretation)^[j] x)) ∧
      out.size ≤ 40000 * powerBudget n c.size (2 ^ n) L := by
  classical
  let f := c.eval Boolean.interpretation
  have ha : absorb f H = f := by
    funext x
    dsimp [absorb]
    split_ifs with hx
    · exact (hstop x hx).symm
    · rfl
  obtain ⟨out, hout, hs⟩ := fixed_power n c (2 ^ n) L hL hLN
  refine ⟨out, fun x hx => ?_, hs⟩
  obtain ⟨t, ht, hp, hfirst, he⟩ := absorb_first_visit f H x (hhalt x hx)
  have hcard : Fintype.card (State n) = 2 ^ n := by simp
  rw [ha, hcard] at he
  have ho : out.eval Boolean.interpretation x = f^[t] x := (hout x).trans he
  exact ⟨ho ▸ hp, t, by simpa [hcard] using ht, ho, hfirst⟩

end IteratedFunctions
