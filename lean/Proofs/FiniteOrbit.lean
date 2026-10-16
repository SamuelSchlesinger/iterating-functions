/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Reconstruction
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Data.Fintype.Card

/-! # First visits in finite functional graphs -/

@[expose] public section

namespace IteratedFunctions

universe u
variable {α : Type u} [Fintype α] (f : α → α)

/-- Every reachable target has a first occurrence before the state-space cardinality. -/
theorem exists_first_visit (P : α → Prop) (x : α) (h : ∃ t, P (f^[t] x)) :
    ∃ t < Fintype.card α, P (f^[t] x) ∧ ∀ k < t, ¬ P (f^[k] x) := by
  classical
  let t := Nat.find h
  have ht : P (f^[t] x) := Nat.find_spec h
  have hmin : ∀ k < t, ¬ P (f^[k] x) := fun k hk => Nat.find_min h hk
  have hinj : Function.Injective (fun i : Fin (t + 1) => f^[i.val] x) := by
    intro i j he
    apply Fin.ext
    by_contra hne
    have bad (a b : ℕ) (hab : a < b) (hbt : b ≤ t) (heq : f^[a] x = f^[b] x) : False := by
      have hr := repeat_reconstruction hab.le heq (by lia : a ≤ t)
      have hlt := repeat_position_lt (T := t) hab
      exact hmin _ (by lia) (hr ▸ ht)
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact bad i.val j.val hij (by have := j.isLt; lia) he
    · exact bad j.val i.val hji (by have := i.isLt; lia) he.symm
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  exact ⟨t, by lia, ht, hmin⟩

def absorb (P : α → Prop) [DecidablePred P] (x : α) : α := if P x then x else f x

omit [Fintype α] in
theorem absorb_iterate_before (P : α → Prop) [DecidablePred P] (x : α) (t : ℕ)
    (h : ∀ j < t, ¬ P (f^[j] x)) : (absorb f P)^[t] x = f^[t] x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (fun j hj => h j (by lia))]
    simp [absorb, h t (by lia)]

omit [Fintype α] in
theorem absorb_iterate_fixed (P : α → Prop) [DecidablePred P] {x : α} (hx : P x) (t : ℕ) :
    (absorb f P)^[t] x = x := by
  induction t with
  | zero => rfl
  | succ t ih => simp [Function.iterate_succ_apply', ih, absorb, hx]

omit [Fintype α] in
theorem absorb_iterate_after (P : α → Prop) [DecidablePred P] (x : α) (t T : ℕ)
    (ht : P (f^[t] x)) (hfirst : ∀ j < t, ¬ P (f^[j] x)) (hle : t ≤ T) :
    (absorb f P)^[T] x = f^[t] x := by
  rw [show T = (T - t) + t by lia, Function.iterate_add_apply,
    absorb_iterate_before f P x t hfirst, absorb_iterate_fixed f P ht]

/-- Iterating the absorbing map for the cardinality returns the first target. -/
theorem absorb_first_visit (P : α → Prop) [DecidablePred P] (x : α)
    (h : ∃ t, P (f^[t] x)) :
    ∃ t < Fintype.card α, P (f^[t] x) ∧ (∀ j < t, ¬ P (f^[j] x)) ∧
      (absorb f P)^[Fintype.card α] x = f^[t] x := by
  obtain ⟨t, ht, hp, hfirst⟩ := exists_first_visit f P x h
  exact ⟨t, ht, hp, hfirst, absorb_iterate_after f P x t _ hp hfirst ht.le⟩

theorem absorb_eventual_iff (P : α → Prop) [DecidablePred P] (x : α) :
    P ((absorb f P)^[Fintype.card α] x) ↔ ∃ t, P (f^[t] x) := by
  constructor
  · intro hp
    by_contra h
    have hh : ∀ j < Fintype.card α, ¬ P (f^[j] x) := fun j _ hj => h ⟨j, hj⟩
    rw [absorb_iterate_before f P x _ hh] at hp
    exact h ⟨_, hp⟩
  · intro h
    obtain ⟨t, _, ht, _, he⟩ := absorb_first_visit f P x h
    rwa [he]

end IteratedFunctions
