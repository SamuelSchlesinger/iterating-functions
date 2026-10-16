/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.CheckpointDepth
public import Proofs.Targets

/-! # First target and halting times from transient depth -/

@[expose] public section

namespace IteratedFunctions

open Cslib.Circuits

universe u
variable {α : Type u} [Finite α]

/-- On a positive instance, making targets absorbing turns first visit time into depth. -/
theorem first_target_depth (f : α → α) (P : α → Prop) [DecidablePred P] (x : α)
    (h : ∃ t, P (f^[t] x)) :
    P (f^[transientDepth (absorb f P) x] x) ∧
      (∀ j < transientDepth (absorb f P) x, ¬ P (f^[j] x)) := by
  classical
  let _ := Fintype.ofFinite α
  obtain ⟨t, _, hp, hfirst⟩ := exists_first_visit f P x h
  let g := absorb f P
  have hbefore : g^[t] x = f^[t] x := absorb_iterate_before f P x t hfirst
  have hfixed : Function.IsFixedPt g (f^[t] x) := by
    change absorb f P (f^[t] x) = f^[t] x
    simp only [absorb, hp, ite_true]
  have hcyclic : f^[t] x ∈ Function.periodicPts g :=
    Function.mk_mem_periodicPts (by decide : 0 < 1) (hfixed.iterate 1)
  have hle : transientDepth g x ≤ t := (periodic_iterate_iff g x t).mp
    (by rw [hbefore]; exact hcyclic)
  have hcancel : g^[transientDepth g x] x = f^[t] x := by
    apply periodic_iterate_inj g (transientDepth_spec g x) hcyclic (t - transientDepth g x)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle, hbefore]
    exact (hfixed.iterate _).symm
  have hbefore' : g^[transientDepth g x] x = f^[transientDepth g x] x :=
    absorb_iterate_before f P x _ (fun j hj => hfirst j (hj.trans_le hle))
  have hP : P (f^[transientDepth g x] x) := by rw [← hbefore', hcancel]; exact hp
  exact ⟨hP, fun j hj => hfirst j (hj.trans_le hle)⟩

/-- Under semantic absorption, the first halting time is exactly the transient depth. -/
theorem halting_depth (f : α → α) (H : α → Prop)
    (hstop : ∀ x, H x → f x = x) (x : α) (h : ∃ t, H (f^[t] x)) :
    H (f^[transientDepth f x] x) ∧ ∀ j < transientDepth f x, ¬ H (f^[j] x) := by
  classical
  have he : absorb f H = f := by
    funext x
    dsimp [absorb]
    split_ifs with hx
    · exact (hstop x hx).symm
    · rfl
  simpa only [he] using first_target_depth f H x h

variable {n : ℕ}

/-- A success flag and exact first target time, with the square-root tradeoff. -/
theorem first_target_time (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) (L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit Boolean.signature n (1 + (n + 2)),
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        ∃ t, p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      (∀ x, out.eval Boolean.interpretation x 0 = true →
        let t := (word fun i : Fin (n + 2) =>
          out.eval Boolean.interpretation x (Fin.natAdd 1 i)).toNat
        p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true ∧
          (∀ j < t,
            p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[j] x) 0 ≠ true) ∧
          t < 2 ^ n) ∧
      out.size ≤ 1040000 * powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L + p.size := by
  let f := c.eval Boolean.interpretation
  let P := fun x => p.eval Boolean.interpretation x 0 = true
  obtain ⟨g, hg, hgs⟩ := absorbing_circuit c p
  have he : g.eval Boolean.interpretation = absorb f P := funext hg
  obtain ⟨depth, hd, hds⟩ := checkpoint_depth_circuit g L hL hLN
  obtain ⟨flag, hf, hfs⟩ := target_reachability c p L hL hLN
  have hdepth := Synthesis.circuit (I := Boolean.interpretation) (s := inputs n) depth id
    (fun i => ⟨i, rfl⟩)
  have hflag := Synthesis.circuit (I := Boolean.interpretation) (s := inputs n) flag id
    (fun i => ⟨i, rfl⟩)
  let output := fun x => Fin.append (flag.eval Boolean.interpretation x)
    (depth.eval Boolean.interpretation x)
  have hs := (hflag.union hdepth).mono Set.Subset.rfl
    (show wires output ⊆ wires (fun x => flag.eval Boolean.interpretation x) ∪
      wires (fun x => depth.eval Boolean.interpretation x) from by
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp only [output, Fin.append_left]⟩
      | right i => exact Or.inr ⟨i, by simp only [output, Fin.append_right]⟩) le_rfl
  obtain ⟨out, ho, hsize⟩ := hs.exists_circuit_outputs
  have hflagout (x) :
      out.eval Boolean.interpretation x 0 = flag.eval Boolean.interpretation x 0 := by
    rw [ho x]
    rfl
  refine ⟨out, fun x => by rw [hflagout, hf], fun x hx => ?_, hsize.trans ?_⟩
  · have hex := (hf x).mp (by rwa [hflagout] at hx)
    have ht : (word fun i : Fin (n + 2) =>
        out.eval Boolean.interpretation x (Fin.natAdd 1 i)).toNat =
        transientDepth (absorb f P) x := by
      simp only [ho x, output, Fin.append_right]
      rw [hd, he]
      apply Nat.mod_eq_of_lt
      have hb : transientDepth (absorb f P) x < 2 ^ n := by
        simpa using transientDepth_lt_card (absorb f P) x
      exact hb.trans_le (Nat.pow_le_pow_right (by decide) (by lia))
    dsimp only
    rw [ht]
    exact ⟨(first_target_depth f P x hex).1, (first_target_depth f P x hex).2,
      by simpa using transientDepth_lt_card (absorb f P) x⟩
  · have hb : powerBudget n g.size (2 ^ n) L ≤
        powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L := by
      unfold powerBudget
      gcongr
    lia

theorem first_target_time_optimized (c : Circuit Boolean.signature n n)
    (p : Circuit Boolean.signature n 1) :
    ∃ out : Circuit Boolean.signature n (1 + (n + 2)),
      (∀ x, out.eval Boolean.interpretation x 0 = true ↔
        ∃ t, p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true) ∧
      (∀ x, out.eval Boolean.interpretation x 0 = true →
        let t := (word fun i : Fin (n + 2) =>
          out.eval Boolean.interpretation x (Fin.natAdd 1 i)).toNat
        p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[t] x) 0 = true ∧
          (∀ j < t,
            p.eval Boolean.interpretation ((c.eval Boolean.interpretation)^[j] x) 0 ≠ true) ∧
          t < 2 ^ n) ∧
      (out.size : ℝ) ≤
        3120000 * optimizedBudget n (c.size + p.size + 4 * n) (2 ^ n) + p.size := by
  obtain ⟨L, hL, hLN, hopt⟩ :=
    powerBudget_optimized n (c.size + p.size + 4 * n) (2 ^ n) le_rfl
  obtain ⟨out, hf, ht, hs⟩ := first_target_time c p L hL hLN
  refine ⟨out, hf, ht, ?_⟩
  have hs' : (out.size : ℝ) ≤
      1040000 * (powerBudget n (c.size + p.size + 4 * n) (2 ^ n) L : ℝ) + p.size := by
    exact_mod_cast hs
  linarith

/-- No recognizer is needed when absorption and eventual halting are semantic hypotheses. -/
theorem halting_time (c : Circuit Boolean.signature n n) (H : State n → Prop)
    (initial : Set (State n)) (hstop : ∀ x, H x → c.eval Boolean.interpretation x = x)
    (hhalt : ∀ x ∈ initial, ∃ t, H ((c.eval Boolean.interpretation)^[t] x)) :
    ∃ out : Circuit Boolean.signature n (n + 2),
      (∀ x ∈ initial, let t := (word (out.eval Boolean.interpretation x)).toNat
        H ((c.eval Boolean.interpretation)^[t] x) ∧
          (∀ j < t, ¬ H ((c.eval Boolean.interpretation)^[j] x)) ∧ t < 2 ^ n) ∧
      (out.size : ℝ) ≤ 3000000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨out, ho, hs⟩ := checkpoint_depth_optimized c
  refine ⟨out, fun x hx => ?_, hs⟩
  dsimp only
  rw [ho]
  have hb : transientDepth (c.eval Boolean.interpretation) x < 2 ^ n := by
    simpa using transientDepth_lt_card (c.eval Boolean.interpretation) x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (hb.trans_le (Nat.pow_le_pow_right (by decide) (by lia)))]
  exact ⟨(halting_depth _ H hstop x (hhalt x hx)).1,
    (halting_depth _ H hstop x (hhalt x hx)).2, hb⟩

end IteratedFunctions
